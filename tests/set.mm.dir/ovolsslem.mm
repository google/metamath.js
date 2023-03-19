include "wss.mm"
include "cr.mm"
include "wa.mm"
include "covol.mm"
include "cfv.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "csup.mm"
include "wceq.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "wcel.mm"
include "wi.mm"
include "sstr2.mm"
include "ad2antrr.mm"
include "anim1d.mm"
include "reximdv.mm"
include "ss2rabdv.mm"
include "3sstr4g.mm"
include "sstr.mm"
include "ovolval.mm"
include "adantr.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "infxrlb.mm"
include "mpan.mm"
include "adantl.mm"
include "eqbrtrd.mm"
include "ralrimiva.mm"
include "syl.mm"
include "ssralv.mm"
include "sylc.mm"
include "wb.mm"
include "ovolcl.mm"
include "infxrgelb.mm"
include "sylancr.mm"
include "mpbird.mm"
include "breqtrrd.mm"

theorem ovolsslem
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cM: class M
  let cN: class N
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vz: setvar z
  let cF: class F
  let cG: class G
  let vk: setvar k
  let wph: wff ph
  let cS: class S
  let cT: class T
  assume ovolss.1: |- M = { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ y = sup ( ran seq 1 ( + , ( ( abs o. - ) o. f ) ) , RR* , < ) ) }
  assume ovolss.2: |- N = { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( B C_ U. ran ( (,) o. f ) /\ y = sup ( ran seq 1 ( + , ( ( abs o. - ) o. f ) ) , RR* , < ) ) }

  disjoint f y
  disjoint A f
  disjoint A y
  disjoint B f
  disjoint B y
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f z
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint F f
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F z
  disjoint G m
  disjoint G z
  disjoint M x
  disjoint N x
  disjoint f k
  disjoint g k
  disjoint B g
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint k z
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph z
  disjoint S f
  disjoint S k
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint T k
  disjoint T y
  assert |- ( ( A C_ B /\ B C_ RR ) -> ( vol* ` A ) <_ ( vol* ` B ) )

  proof
    cA
    cB
    wss
    #
    cB
    cr
    wss
    #
    wa
    #
    cA
    covol
    cfv
    #
    cN
    cxr
    clt
    cinf
    #
    cB
    covol
    cfv
    #
    cle
    @2
    @3
    @4
    cle
    wbr
    #
    @3
    vx
    cv
    #
    cle
    wbr
    #
    vx
    cN
    wral
    #
    @2
    cN
    cM
    wss
    @8
    vx
    cM
    wral
    #
    @9
    @2
    cB
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    #
    wss
    #
    vy
    cv
    #
    caddc
    cabs
    cmin
    ccom
    @11
    ccom
    c1
    cseq
    crn
    cxr
    clt
    csup
    wceq
    #
    wa
    #
    vf
    cle
    cr
    cr
    cxp
    cin
    cn
    cmap
    co
    #
    wrex
    #
    vy
    cxr
    crab
    #
    cA
    @12
    wss
    #
    @15
    wa
    #
    vf
    @17
    wrex
    #
    vy
    cxr
    crab
    #
    cN
    cM
    @2
    @18
    @22
    vy
    cxr
    @2
    @14
    cxr
    wcel
    #
    wa
    #
    @16
    @21
    vf
    @17
    @25
    @13
    @20
    @15
    @0
    @13
    @20
    wi
    @1
    @24
    cA
    cB
    @12
    sstr2
    ad2antrr
    anim1d
    reximdv
    ss2rabdv
    ovolss.2
    ovolss.1
    3sstr4g
    @2
    cA
    cr
    wss
    #
    @10
    cA
    cB
    cr
    sstr
    #
    @26
    @8
    vx
    cM
    @26
    @7
    cM
    wcel
    #
    wa
    @3
    cM
    cxr
    clt
    cinf
    #
    @7
    cle
    @26
    @3
    @29
    wceq
    @28
    vy
    cA
    vf
    cM
    ovolss.1
    ovolval
    adantr
    @28
    @29
    @7
    cle
    wbr
    #
    @26
    cM
    cxr
    wss
    @28
    @30
    cM
    @23
    cxr
    ovolss.1
    @22
    vy
    cxr
    ssrab2
    eqsstri
    cM
    @7
    infxrlb
    mpan
    adantl
    eqbrtrd
    ralrimiva
    syl
    @8
    vx
    cN
    cM
    ssralv
    sylc
    @2
    cN
    cxr
    wss
    @3
    cxr
    wcel
    #
    @6
    @9
    wb
    cN
    @19
    cxr
    ovolss.2
    @18
    vy
    cxr
    ssrab2
    eqsstri
    @2
    @26
    @31
    @27
    cA
    ovolcl
    syl
    vx
    cN
    @3
    infxrgelb
    sylancr
    mpbird
    @1
    @5
    @4
    wceq
    @0
    vy
    cB
    vf
    cN
    ovolss.2
    ovolval
    adantl
    breqtrrd
end
