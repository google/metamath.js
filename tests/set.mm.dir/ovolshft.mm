include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "cinf.mm"
include "covol.mm"
include "cfv.mm"
include "eqid.mm"
include "ovolshftlem2.mm"
include "cneg.mm"
include "wcel.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "renegcld.mm"
include "shft2rab.mm"
include "eqssd.mm"
include "infeq1d.mm"
include "ovolval.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem ovolshft
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cM: class M
  assume ovolshft.1: |- ( ph -> A C_ RR )
  assume ovolshft.2: |- ( ph -> C e. RR )
  assume ovolshft.3: |- ( ph -> B = { x e. RR | ( x - C ) e. A } )

  disjoint A x
  disjoint C x
  disjoint f g
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint f m
  disjoint C f
  disjoint g m
  disjoint C g
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint C m
  disjoint C n
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint F n
  disjoint F x
  disjoint G f
  disjoint G n
  disjoint G y
  disjoint B f
  disjoint B g
  disjoint B n
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint M g
  disjoint M z
  disjoint f ph
  disjoint g ph
  disjoint n ph
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( vol* ` A ) = ( vol* ` B ) )

  proof
    wph
    cA
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    vy
    cv
    caddc
    cabs
    cmin
    ccom
    #
    @0
    ccom
    c1
    cseq
    crn
    cxr
    clt
    csup
    wceq
    wa
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
    vy
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cB
    cioo
    vg
    cv
    #
    ccom
    crn
    cuni
    wss
    vz
    cv
    caddc
    @1
    @5
    ccom
    c1
    cseq
    crn
    cxr
    clt
    csup
    wceq
    wa
    vg
    @2
    wrex
    vz
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cA
    covol
    cfv
    #
    cB
    covol
    cfv
    #
    wph
    cxr
    @3
    @6
    clt
    wph
    @3
    @6
    wph
    vx
    vz
    vy
    cA
    cB
    cC
    vg
    vf
    @6
    ovolshft.1
    ovolshft.2
    ovolshft.3
    @6
    eqid
    #
    ovolshftlem2
    wph
    vw
    vy
    vz
    cB
    cA
    cC
    cneg
    vf
    vg
    @3
    wph
    cB
    vx
    cv
    cC
    cmin
    co
    cA
    wcel
    #
    vx
    cr
    crab
    cr
    ovolshft.3
    @11
    vx
    cr
    ssrab2
    syl6eqss
    #
    wph
    cC
    ovolshft.2
    renegcld
    wph
    vx
    vw
    cA
    cB
    cC
    ovolshft.1
    ovolshft.2
    ovolshft.3
    shft2rab
    @3
    eqid
    #
    ovolshftlem2
    eqssd
    infeq1d
    wph
    cA
    cr
    wss
    @8
    @4
    wceq
    ovolshft.1
    vy
    cA
    vf
    @3
    @13
    ovolval
    syl
    wph
    cB
    cr
    wss
    @9
    @7
    wceq
    @12
    vz
    cB
    vg
    @6
    @10
    ovolval
    syl
    3eqtr4d
end
