include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cdm.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "csb.mm"
include "wceq.mm"
include "wral.mm"
include "caddc.mm"
include "cc0.mm"
include "cfzo.mm"
include "wi.mm"
include "fz0add1fz1.mm"
include "simpl.mm"
include "adantr.mm"
include "wb.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "csbeq1.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "anim1i.mm"
include "simpr.mm"
include "ad3antlr.mm"
include "fargshiftfv.mm"
include "imp.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "rspcdv.mm"
include "ex.mm"
include "com23.mm"
include "mpancom.mm"
include "com24.mm"
include "imp31.mm"
include "ralrimiv.mm"

theorem fargshiftfva
  let vx: setvar x
  let cP: class P
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let vl: setvar l
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume fargshift.g: |- G = ( x e. ( 0 ..^ ( # ` F ) ) |-> ( F ` ( x + 1 ) ) )

  disjoint F x
  disjoint E x
  disjoint F k
  disjoint F l
  disjoint k l
  disjoint k x
  disjoint l x
  disjoint N x
  disjoint E k
  disjoint G k
  disjoint N k
  disjoint P k
  disjoint E l
  disjoint N l
  disjoint P l
  disjoint k x
  disjoint X x
  disjoint F y
  disjoint F z
  disjoint k y
  disjoint k z
  disjoint l y
  disjoint l z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint E y
  disjoint E z
  disjoint G y
  disjoint G z
  disjoint N y
  disjoint N z
  assert |- ( ( N e. NN0 /\ F : ( 1 ... N ) --> dom E ) -> ( A. k e. ( 1 ... N ) ( E ` ( F ` k ) ) = [_ k / x ]_ P -> A. l e. ( 0 ..^ N ) ( E ` ( G ` l ) ) = [_ ( l + 1 ) / x ]_ P ) )

  proof
    cN
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    cE
    cdm
    cF
    wf
    #
    wa
    #
    vk
    cv
    #
    cF
    cfv
    #
    cE
    cfv
    #
    vx
    @4
    cP
    csb
    #
    wceq
    #
    vk
    @1
    wral
    #
    vl
    cv
    #
    cG
    cfv
    #
    cE
    cfv
    #
    vx
    @10
    c1
    caddc
    co
    #
    cP
    csb
    #
    wceq
    #
    vl
    cc0
    cN
    cfzo
    co
    #
    wral
    @3
    @9
    wa
    @15
    vl
    @16
    @0
    @2
    @9
    @10
    @16
    wcel
    #
    @15
    wi
    @0
    @17
    @9
    @2
    @15
    @0
    @17
    @9
    @2
    @15
    wi
    wi
    #
    @13
    @1
    wcel
    #
    @0
    @17
    wa
    #
    @18
    cN
    @10
    fz0add1fz1
    @19
    @20
    wa
    #
    @2
    @9
    @15
    @21
    @2
    @9
    @15
    wi
    @21
    @2
    wa
    #
    @8
    @15
    vk
    @13
    @1
    @21
    @19
    @2
    @19
    @20
    simpl
    adantr
    @22
    @4
    @13
    wceq
    #
    wa
    #
    @8
    @13
    cF
    cfv
    #
    cE
    cfv
    #
    @14
    wceq
    #
    @15
    @23
    @8
    @27
    wb
    @22
    @23
    @6
    @26
    @7
    @14
    @23
    @5
    @25
    cE
    @4
    @13
    cF
    fveq2
    fveq2d
    vx
    @4
    @13
    cP
    csbeq1
    eqeq12d
    adantl
    @24
    @26
    @12
    @14
    @24
    @25
    @11
    cE
    @24
    @3
    @17
    @25
    @11
    wceq
    @22
    @3
    @23
    @21
    @0
    @2
    @20
    @0
    @19
    @0
    @17
    simpl
    adantl
    anim1i
    adantr
    @20
    @17
    @19
    @2
    @23
    @0
    @17
    simpr
    ad3antlr
    @3
    @17
    wa
    @11
    @25
    @3
    @17
    @11
    @25
    wceq
    vx
    cE
    cF
    cG
    cN
    @10
    fargshift.g
    fargshiftfv
    imp
    eqcomd
    syl2anc
    fveq2d
    eqeq1d
    bitrd
    rspcdv
    ex
    com23
    mpancom
    ex
    com24
    imp31
    ralrimiv
    ex
end
