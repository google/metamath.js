include "cdomn.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "simp1.mm"
include "cn0.mm"
include "wf.mm"
include "eqid.mm"
include "coe1f.mm"
include "3ad2ant2.mm"
include "crg.mm"
include "domnring.mm"
include "deg1nn0cl.mm"
include "syl3an1.mm"
include "ffvelrnd.mm"
include "deg1ldg.mm"
include "domnrrg.mm"
include "syl3anc.mm"

theorem deg1ldgdomn
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cE: class E
  let cF: class F
  let c.0: class .0.
  assume deg1z.d: |- D = ( deg1 ` R )
  assume deg1z.p: |- P = ( Poly1 ` R )
  assume deg1z.z: |- .0. = ( 0g ` P )
  assume deg1nn0cl.b: |- B = ( Base ` P )
  assume deg1ldgdomn.e: |- E = ( RLReg ` R )
  assume deg1ldgdomn.a: |- A = ( coe1 ` F )


  assert |- ( ( R e. Domn /\ F e. B /\ F =/= .0. ) -> ( A ` ( D ` F ) ) e. E )

  proof
    cR
    cdomn
    wcel
    #
    cF
    cB
    wcel
    #
    cF
    c.0
    wne
    #
    w3a
    #
    @0
    cF
    cD
    cfv
    #
    cA
    cfv
    #
    cR
    cbs
    cfv
    #
    wcel
    @5
    cR
    c0g
    cfv
    #
    wne
    #
    @5
    cE
    wcel
    @0
    @1
    @2
    simp1
    @3
    cn0
    @6
    @4
    cA
    @1
    @0
    cn0
    @6
    cA
    wf
    @2
    cA
    cB
    cP
    cR
    cF
    @6
    deg1ldgdomn.a
    deg1nn0cl.b
    deg1z.p
    @6
    eqid
    #
    coe1f
    3ad2ant2
    @0
    cR
    crg
    wcel
    #
    @1
    @2
    @4
    cn0
    wcel
    cR
    domnring
    #
    cB
    cD
    cP
    cR
    cF
    c.0
    deg1z.d
    deg1z.p
    deg1z.z
    deg1nn0cl.b
    deg1nn0cl
    syl3an1
    ffvelrnd
    @0
    @10
    @1
    @2
    @8
    @11
    cA
    cB
    cD
    cP
    cR
    cF
    @7
    c.0
    deg1z.d
    deg1z.p
    deg1z.z
    deg1nn0cl.b
    @7
    eqid
    #
    deg1ldgdomn.a
    deg1ldg
    syl3an1
    @6
    cR
    cE
    @5
    @7
    @9
    deg1ldgdomn.e
    @12
    domnrrg
    syl3anc
end
