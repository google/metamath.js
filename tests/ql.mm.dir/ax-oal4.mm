
axiom ax-oal4
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume oal4.1: |- a =< b '
  assume oal4.2: |- c =< d '
  assert |- ( ( a v b ) ^ ( c v d ) ) =< ( b v ( a ^ ( c v ( ( a v c ) ^ ( b v d ) ) ) ) )
end
