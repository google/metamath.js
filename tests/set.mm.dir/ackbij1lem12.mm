include "com.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cdif.mm"
include "coa.mm"
include "co.mm"
include "wf.mm"
include "ackbij1lem10.mm"
include "ackbij1lem11.mm"
include "ffvelrn.mm"
include "sylancr.mm"
include "difssd.mm"
include "syldan.mm"
include "nnaword1.mm"
include "syl2anc.mm"
include "cun.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "a1i.mm"
include "ackbij1lem9.mm"
include "syl3anc.mm"
include "undif.mm"
include "biimpi.mm"
include "adantl.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "sseqtrd.mm"

theorem ackbij1lem12
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  assert |- ( ( B e. ( ~P _om i^i Fin ) /\ A C_ B ) -> ( F ` A ) C_ ( F ` B ) )

  proof
    cB
    com
    cpw
    cfn
    cin
    #
    wcel
    #
    cA
    cB
    wss
    #
    wa
    #
    cA
    cF
    cfv
    #
    @4
    cB
    cA
    cdif
    #
    cF
    cfv
    #
    coa
    co
    #
    cB
    cF
    cfv
    #
    @3
    @4
    com
    wcel
    #
    @6
    com
    wcel
    #
    @4
    @7
    wss
    @3
    @0
    com
    cF
    wf
    #
    cA
    @0
    wcel
    #
    @9
    vx
    vy
    cF
    ackbij.f
    ackbij1lem10
    #
    vx
    vy
    cB
    cA
    cF
    ackbij.f
    ackbij1lem11
    #
    @0
    com
    cA
    cF
    ffvelrn
    sylancr
    @3
    @11
    @5
    @0
    wcel
    #
    @10
    @13
    @1
    @2
    @5
    cB
    wss
    @15
    @3
    cB
    cA
    difssd
    vx
    vy
    cB
    @5
    cF
    ackbij.f
    ackbij1lem11
    syldan
    #
    @0
    com
    @5
    cF
    ffvelrn
    sylancr
    @4
    @6
    nnaword1
    syl2anc
    @3
    cA
    @5
    cun
    #
    cF
    cfv
    #
    @7
    @8
    @3
    @12
    @15
    cA
    @5
    cin
    c0
    wceq
    #
    @18
    @7
    wceq
    @14
    @16
    @19
    @3
    cA
    cB
    disjdif
    a1i
    vx
    vy
    cA
    @5
    cF
    ackbij.f
    ackbij1lem9
    syl3anc
    @3
    @17
    cB
    cF
    @2
    @17
    cB
    wceq
    #
    @1
    @2
    @20
    cA
    cB
    undif
    biimpi
    adantl
    fveq2d
    eqtr3d
    sseqtrd
end
