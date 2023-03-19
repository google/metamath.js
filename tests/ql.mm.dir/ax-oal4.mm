
axiom ax-oal4
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume oal4.1: |- a =< b '
  assume oal4.2: |- c =< d '
  assert |- ( ( a v b ) ^ ( c v d ) ) =< ( b v ( a ^ ( c v ( ( a v c ) ^ ( b v d ) ) ) ) )
end
