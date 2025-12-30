import os
#os.environ["CUDA_VISIBLE_DEVICES"] = "0"
import numpy as np
import tensorflow as tf
#from tensorflow.keras.models import *
#from keras.layers.merge import concatenate
#from tensorflow.keras.layers import Input, Conv2D, MaxPooling2D, UpSampling2D, Dropout, Cropping2D
#from tensorflow.keras.optimizers import *
from tensorflow.keras.callbacks import ModelCheckpoint, LearningRateScheduler

def Unet(img_rows=512,img_cols=512):
  inputs = tf.keras.layers.Input((img_rows, img_cols,1))

  conv1 = tf.keras.layers.Conv2D(64, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(inputs)
  conv1 = tf.keras.layers.Conv2D(64, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(conv1)
  pool1 = tf.keras.layers.MaxPooling2D(pool_size=(2, 2))(conv1)
  conv2 = tf.keras.layers.Conv2D(128, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(pool1)
  conv2 = tf.keras.layers.Conv2D(128, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(conv2)
  pool2 = tf.keras.layers.MaxPooling2D(pool_size=(2, 2))(conv2)
  conv3 = tf.keras.layers.Conv2D(256, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(pool2)
  conv3 = tf.keras.layers.Conv2D(256, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(conv3)
  pool3 = tf.keras.layers.MaxPooling2D(pool_size=(2, 2))(conv3)
  conv4 = tf.keras.layers.Conv2D(512, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(pool3)
  conv4 = tf.keras.layers.Conv2D(512, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(conv4)
  drop4 = tf.keras.layers.Dropout(0.5)(conv4)
  pool4 = tf.keras.layers.MaxPooling2D(pool_size=(2, 2))(drop4)
  conv5 = tf.keras.layers.Conv2D(1024, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(pool4)
  conv5 = tf.keras.layers.Conv2D(1024, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(conv5)
  drop5 = tf.keras.layers.Dropout(0.5)(conv5)
  up6 = tf.keras.layers.Conv2D(512, 2, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(tf.keras.layers.UpSampling2D(size = (2,2))(drop5))
  merge6 = tf.keras.layers.concatenate([drop4,up6],axis = 3)
  conv6 = tf.keras.layers.Conv2D(512, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(merge6)
  conv6 = tf.keras.layers.Conv2D(512, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(conv6)
  up7 = tf.keras.layers.Conv2D(256, 2, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(tf.keras.layers.UpSampling2D(size = (2,2))(conv6))
  merge7 = tf.keras.layers.concatenate([conv3,up7],axis = 3)
  conv7 = tf.keras.layers.Conv2D(256, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(merge7)
  conv7 = tf.keras.layers.Conv2D(256, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(conv7)
  up8 = tf.keras.layers.Conv2D(128, 2, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(tf.keras.layers.UpSampling2D(size = (2,2))(conv7))
  merge8 = tf.keras.layers.concatenate([conv2,up8],axis = 3)
  conv8 = tf.keras.layers.Conv2D(128, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(merge8)
  conv8 = tf.keras.layers.Conv2D(128, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(conv8)

  up9 = tf.keras.layers.Conv2D(64, 2, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(tf.keras.layers.UpSampling2D(size = (2,2))(conv8))
  merge9 = tf.keras.layers.concatenate([conv1,up9],axis = 3)
  conv9 = tf.keras.layers.Conv2D(64, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(merge9)
  conv9 = tf.keras.layers.Conv2D(64, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(conv9)
  conv9 = tf.keras.layers.Conv2D(2, 3, activation = 'relu', padding = 'same', kernel_initializer = 'he_normal')(conv9)
  conv10 = tf.keras.layers.Conv2D(1, 1, activation = 'sigmoid')(conv9)
  model = tf.keras.Model(inputs = inputs, outputs = conv10)
  model.compile(optimizer = tf.keras.optimizers.Adam(lr = 1e-4), loss = 'binary_crossentropy', metrics = ['accuracy'])
  return model
import os
def train(imgs_train, imgs_mask_train,batch_size,n_epoch):
  session_config = tf.ConfigProto(allow_soft_placement=True, log_device_placement=False)
  session_config.gpu_options.allow_growth=True
  session_config.gpu_options.per_process_gpu_memory_fraction = 0.8
  tf.keras.backend.clear_session()
  model = Unet()
  print("got unet")
  model_checkpoint = ModelCheckpoint('unet.hdf5', monitor='loss',verbose=1, save_best_only=True)
  print('Fitting model...')
  model.fit(imgs_train, imgs_mask_train, batch_size = batch_size,epochs=n_epoch, verbose =1, validation_split = 0.2, shuffle = True, callbacks=[model_checkpoint])
  model.save_weights('./results/bard.h5', overwrite=True)

from skimage import io
imgs_train = io.imread('C:/Users/ATRC237_GUO/Desktop/EM/train-volume.tif')[:,:,:,np.newaxis]
imgs_mask_train = io.imread('C:/Users/ATRC237_GUO/Desktop/EM/train-labels.tif')[:,:,:,np.newaxis]
image_test = io.imread('C:/Users/ATRC237_GUO/Desktop/EM/test-volume.tif')[:,:,:,np.newaxis]

train(imgs_train, imgs_mask_train,batch_size=1,n_epoch=10)
