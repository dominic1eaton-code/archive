#
#
#

# project
PROJECT_NAME=kazi-client
ng new --package-manager=npm --style=sass --server-routing --routing --ssr --standalone=false --strict --view-encapsulation=ShadowDom ${PROJECT_NAME}

# packages
npm install --save bulma

# developer cli
ng build --configuration production
ng serve