include "wcel.mm"
include "wa.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "symgfixf1.mm"
include "adantl.mm"
include "symgfixfo.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem symgfixf1o
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let vq: setvar q
  let vg: setvar g
  let vp: setvar p
  let vi: setvar i
  let vs: setvar s
  let vj: setvar j
  assume symgfixf.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume symgfixf.q: |- Q = { q e. P | ( q ` K ) = K }
  assume symgfixf.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgfixf.h: |- H = ( q e. Q |-> ( q |` ( N \ { K } ) ) )

  disjoint K q
  disjoint P q
  disjoint N q
  disjoint Q q
  disjoint S q
  disjoint H g
  disjoint H p
  disjoint g p
  disjoint K g
  disjoint K i
  disjoint K p
  disjoint g i
  disjoint i p
  disjoint N g
  disjoint N i
  disjoint N p
  disjoint g q
  disjoint i q
  disjoint p q
  disjoint Q g
  disjoint Q p
  disjoint H s
  disjoint K s
  disjoint N s
  disjoint Q s
  disjoint S p
  disjoint S s
  disjoint p s
  disjoint S i
  disjoint S j
  disjoint i j
  disjoint i s
  disjoint j s
  disjoint V p
  disjoint V j
  disjoint V s
  disjoint K j
  disjoint N j
  assert |- ( ( N e. V /\ K e. N ) -> H : Q -1-1-onto-> S )

  proof
    cN
    cV
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    cQ
    cS
    cH
    wf1
    #
    cQ
    cS
    cH
    wfo
    cQ
    cS
    cH
    wf1o
    @1
    @2
    @0
    cP
    cQ
    cS
    cH
    cK
    cN
    vq
    symgfixf.p
    symgfixf.q
    symgfixf.s
    symgfixf.h
    symgfixf1
    adantl
    cP
    cQ
    cS
    cH
    cK
    cN
    cV
    vq
    symgfixf.p
    symgfixf.q
    symgfixf.s
    symgfixf.h
    symgfixfo
    cQ
    cS
    cH
    df-f1o
    sylanbrc
end
