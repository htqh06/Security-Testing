fact Authenticity {
  all a: Action - LoginAction | some l: LoginAction | l.user = a.user
}


