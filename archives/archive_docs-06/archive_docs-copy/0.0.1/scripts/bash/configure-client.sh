#
#
#

# configure angular client
ng new --package-manager=npm --style=sass --server-routing --routing --ssr --standalone=false --strict --view-encapsulation=ShadowDom umuthi-client

ng g module core
ng g component core/header
ng g component core/footer
ng g component core/primary-nav
ng g component core/secondary-nav

ng g module features --routing
ng g component features/landing
ng g component features/login
ng g component features/dashboard
ng g component features/portfolio

npm install --save bulma

ng build --configuration production
ng server
