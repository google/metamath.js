
axiom ax-oa6
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e
  param wvf: term f
  assume oal6.1: |- a =< b '
  assume oal6.2: |- c =< d '
  assume oal6.3: |- e =< f '
  assert |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( e v f ) ) =< ( b v ( a ^ ( c v ( ( ( a v c ) ^ ( b v d ) ) ^ ( ( ( a v e ) ^ ( b v f ) ) v ( ( c v e ) ^ ( d v f ) ) ) ) ) ) )
end
