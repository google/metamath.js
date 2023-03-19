include "cr.mm"
include "wss.mm"
include "cxr.mm"
include "wf.mm"
include "wcel.mm"
include "w3a.mm"
include "clsp.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "crn.mm"
include "clt.mm"
include "cinf.mm"
include "cv.mm"
include "wral.mm"
include "cvv.mm"
include "wceq.mm"
include "simp2.mm"
include "reex.mm"
include "ssex.mm"
include "3ad2ant1.mm"
include "xrex.mm"
include "a1i.mm"
include "fex2.mm"
include "syl3anc.mm"
include "limsupval.mm"
include "syl.mm"
include "breq2d.mm"
include "wb.mm"
include "limsupgf.mm"
include "frn.mm"
include "ax-mp.mm"
include "simp3.mm"
include "infxrgelb.mm"
include "sylancr.mm"
include "wfn.mm"
include "ffn.mm"
include "breq2.mm"
include "ralrn.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem limsuple
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let cM: class M
  let cC: class C
  assume limsupval.1: |- G = ( k e. RR |-> sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )

  disjoint F k
  disjoint A j
  disjoint B j
  disjoint j k
  disjoint F j
  disjoint G j
  disjoint k x
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint f k
  disjoint G x
  disjoint M k
  disjoint C j
  disjoint C k
  disjoint C x
  disjoint j x
  assert |- ( ( B C_ RR /\ F : B --> RR* /\ A e. RR* ) -> ( A <_ ( limsup ` F ) <-> A. j e. RR A <_ ( G ` j ) ) )

  proof
    cB
    cr
    wss
    #
    cB
    cxr
    cF
    wf
    #
    cA
    cxr
    wcel
    #
    w3a
    #
    cA
    cF
    clsp
    cfv
    #
    cle
    wbr
    cA
    cG
    crn
    #
    cxr
    clt
    cinf
    #
    cle
    wbr
    #
    cA
    vj
    cv
    cG
    cfv
    #
    cle
    wbr
    #
    vj
    cr
    wral
    #
    @3
    @4
    @6
    cA
    cle
    @3
    cF
    cvv
    wcel
    #
    @4
    @6
    wceq
    @3
    @1
    cB
    cvv
    wcel
    #
    cxr
    cvv
    wcel
    #
    @11
    @0
    @1
    @2
    simp2
    @0
    @1
    @12
    @2
    cB
    cr
    reex
    ssex
    3ad2ant1
    @13
    @3
    xrex
    a1i
    cB
    cxr
    cF
    cvv
    cvv
    fex2
    syl3anc
    vk
    cF
    cG
    cvv
    limsupval.1
    limsupval
    syl
    breq2d
    @3
    @7
    cA
    vx
    cv
    #
    cle
    wbr
    #
    vx
    @5
    wral
    #
    @10
    @3
    @5
    cxr
    wss
    #
    @2
    @7
    @16
    wb
    cr
    cxr
    cG
    wf
    #
    @17
    vk
    cF
    cG
    limsupval.1
    limsupgf
    #
    cr
    cxr
    cG
    frn
    ax-mp
    @0
    @1
    @2
    simp3
    vx
    @5
    cA
    infxrgelb
    sylancr
    cG
    cr
    wfn
    #
    @16
    @10
    wb
    @18
    @20
    @19
    cr
    cxr
    cG
    ffn
    ax-mp
    @15
    @9
    vx
    vj
    cr
    cG
    @14
    @8
    cA
    cle
    breq2
    ralrn
    ax-mp
    syl6bb
    bitrd
end
