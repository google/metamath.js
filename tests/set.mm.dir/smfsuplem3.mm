include "nfv.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "ciin.mm"
include "cuni.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "cuz.mm"
include "cz.mm"
include "wcel.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "wceq.mm"
include "fveq2.mm"
include "dmeqd.mm"
include "csmblfn.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "smfdmss.mm"
include "iinssd.mm"
include "sstrd.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "ne0d.mm"
include "adantr.mm"
include "wf.mm"
include "csalg.mm"
include "ffvelrnda.mm"
include "smff.mm"
include "adantlr.mm"
include "iinss2.mm"
include "adantl.mm"
include "sseli.mm"
include "sseldd.mm"
include "adantll.mm"
include "rabeq2i.mm"
include "simprbi.mm"
include "suprclrnmpt.mm"
include "fmptd.mm"
include "simpr.mm"
include "smfsuplem2.mm"
include "issmfle2d.mm"

theorem smfsuplem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let va: setvar a
  let vk: setvar k
  assume smfsuplem3.m: |- ( ph -> M e. ZZ )
  assume smfsuplem3.z: |- Z = ( ZZ>= ` M )
  assume smfsuplem3.s: |- ( ph -> S e. SAlg )
  assume smfsuplem3.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smfsuplem3.d: |- D = { x e. |^|_ n e. Z dom ( F ` n ) | E. y e. RR A. n e. Z ( ( F ` n ) ` x ) <_ y }
  assume smfsuplem3.g: |- G = ( x e. D |-> sup ( ran ( n e. Z |-> ( ( F ` n ) ` x ) ) , RR , < ) )

  disjoint D n
  disjoint D x
  disjoint D y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint M n
  disjoint S n
  disjoint S y
  disjoint Z n
  disjoint Z x
  disjoint Z y
  disjoint n ph
  disjoint ph y
  disjoint ph x
  disjoint G a
  disjoint S a
  disjoint a n
  disjoint a y
  disjoint a ph
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    cD
    cS
    cG
    va
    wph
    va
    nfv
    smfsuplem3.s
    wph
    cD
    vn
    cZ
    vn
    cv
    #
    cF
    cfv
    #
    cdm
    #
    ciin
    #
    cS
    cuni
    #
    cD
    @3
    wss
    wph
    cD
    vx
    cv
    #
    @1
    cfv
    #
    vy
    cv
    cle
    wbr
    vn
    cZ
    wral
    vy
    cr
    wrex
    #
    vx
    @3
    crab
    @3
    smfsuplem3.d
    @7
    vx
    @3
    ssrab2
    eqsstri
    #
    a1i
    wph
    vn
    cZ
    @2
    @4
    cM
    cF
    cfv
    #
    cdm
    #
    cM
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    #
    cM
    @11
    wcel
    smfsuplem3.m
    cM
    uzid
    syl
    smfsuplem3.z
    syl6eleqr
    #
    @0
    cM
    wceq
    @1
    @9
    @0
    cM
    cF
    fveq2
    dmeqd
    wph
    @10
    cS
    @9
    smfsuplem3.s
    wph
    cZ
    cS
    csmblfn
    cfv
    #
    cM
    cF
    smfsuplem3.f
    @13
    ffvelrnd
    @10
    eqid
    smfdmss
    iinssd
    sstrd
    wph
    vx
    cD
    vn
    cZ
    @6
    cmpt
    crn
    cr
    clt
    csup
    cr
    cG
    wph
    @5
    cD
    wcel
    #
    wa
    #
    vn
    vy
    cZ
    @6
    @16
    vn
    nfv
    wph
    cZ
    c0
    wne
    @15
    wph
    cZ
    cM
    @13
    ne0d
    adantr
    @16
    @0
    cZ
    wcel
    #
    wa
    @2
    cr
    @5
    @1
    wph
    @17
    @2
    cr
    @1
    wf
    @15
    wph
    @17
    wa
    @2
    cS
    @1
    wph
    cS
    csalg
    wcel
    #
    @17
    smfsuplem3.s
    adantr
    wph
    cZ
    @14
    @0
    cF
    smfsuplem3.f
    ffvelrnda
    @2
    eqid
    smff
    adantlr
    @15
    @17
    @5
    @2
    wcel
    wph
    @15
    @17
    wa
    @3
    @2
    @5
    @17
    @3
    @2
    wss
    @15
    vn
    cZ
    @2
    iinss2
    adantl
    @15
    @5
    @3
    wcel
    #
    @17
    cD
    @3
    @5
    @8
    sseli
    adantr
    sseldd
    adantll
    ffvelrnd
    @15
    @7
    wph
    @15
    @19
    @7
    @7
    vx
    cD
    @3
    smfsuplem3.d
    rabeq2i
    simprbi
    adantl
    suprclrnmpt
    smfsuplem3.g
    fmptd
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    vx
    vy
    @20
    cD
    cS
    vn
    cF
    cG
    cM
    cZ
    wph
    @12
    @21
    smfsuplem3.m
    adantr
    smfsuplem3.z
    wph
    @18
    @21
    smfsuplem3.s
    adantr
    wph
    cZ
    @14
    cF
    wf
    @21
    smfsuplem3.f
    adantr
    smfsuplem3.d
    smfsuplem3.g
    wph
    @21
    simpr
    smfsuplem2
    issmfle2d
end
