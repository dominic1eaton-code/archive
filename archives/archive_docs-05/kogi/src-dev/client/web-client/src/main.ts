import { ViewEncapsulation } from '@angular/core';
import { platformBrowser } from '@angular/platform-browser';
import { AppModule } from './app/app-module';

platformBrowser().bootstrapModule(AppModule, {
  ngZoneEventCoalescing: true,
  defaultEncapsulation: ViewEncapsulation.ShadowDom
})
  .catch(err => console.error(err));
