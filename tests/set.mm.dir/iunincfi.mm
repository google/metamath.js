include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wrex.mm"
include "eliun.mm"
include "biimpi.mm"
include "adantl.mm"
include "w3a.mm"
include "wa.mm"
include "cuz.mm"
include "elfzuz3.mm"
include "cfzo.mm"
include "c1.mm"
include "caddc.mm"
include "simpll.mm"
include "elfzuz.mm"
include "fzoss1.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "adantll.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "syl2anc.mm"
include "ssinc.mm"
include "3adant3.mm"
include "simp3.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "imp.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "eluzfz2.mm"
include "ssiun2s.mm"
include "eqssd.mm"

theorem iunincfi
  let wph: wff ph
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vx: setvar x
  assume iunincfi.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume iunincfi.2: |- ( ( ph /\ n e. ( M ..^ N ) ) -> ( F ` n ) C_ ( F ` ( n + 1 ) ) )

  disjoint F n
  disjoint M n
  disjoint N n
  disjoint n ph
  disjoint F m
  disjoint m n
  disjoint F x
  disjoint n x
  disjoint M m
  disjoint M x
  disjoint N m
  disjoint N x
  disjoint m ph
  disjoint ph x
  assert |- ( ph -> U_ n e. ( M ... N ) ( F ` n ) = ( F ` N ) )

  proof
    wph
    vn
    cM
    cN
    cfz
    co
    #
    vn
    cv
    #
    cF
    cfv
    #
    ciun
    #
    cN
    cF
    cfv
    #
    wph
    vx
    cv
    #
    @4
    wcel
    #
    vx
    @3
    wral
    @3
    @4
    wss
    wph
    @6
    vx
    @3
    wph
    @5
    @3
    wcel
    #
    @5
    @2
    wcel
    #
    vn
    @0
    wrex
    #
    @6
    @7
    @9
    wph
    @7
    @9
    vn
    @5
    @0
    @2
    eliun
    biimpi
    adantl
    wph
    @9
    @6
    wph
    @8
    @6
    vn
    @0
    wph
    @1
    @0
    wcel
    #
    @8
    @6
    wph
    @10
    @8
    w3a
    @2
    @4
    @5
    wph
    @10
    @2
    @4
    wss
    @8
    wph
    @10
    wa
    #
    vm
    cF
    @1
    cN
    @10
    cN
    @1
    cuz
    cfv
    wcel
    wph
    @1
    cM
    cN
    elfzuz3
    adantl
    @11
    vm
    cv
    #
    @1
    cN
    cfzo
    co
    #
    wcel
    #
    wa
    wph
    @12
    cM
    cN
    cfzo
    co
    #
    wcel
    #
    @12
    cF
    cfv
    #
    @12
    c1
    caddc
    co
    #
    cF
    cfv
    #
    wss
    #
    wph
    @10
    @14
    simpll
    @10
    @14
    @16
    wph
    @10
    @14
    wa
    @13
    @15
    @12
    @10
    @13
    @15
    wss
    #
    @14
    @10
    @1
    cM
    cuz
    cfv
    #
    wcel
    @21
    @1
    cM
    cN
    elfzuz
    @1
    cM
    cN
    fzoss1
    syl
    adantr
    @10
    @14
    simpr
    sseldd
    adantll
    wph
    @1
    @15
    wcel
    #
    wa
    #
    @2
    @1
    c1
    caddc
    co
    #
    cF
    cfv
    #
    wss
    #
    wi
    wph
    @16
    wa
    #
    @20
    wi
    vn
    vm
    @1
    @12
    wceq
    #
    @24
    @28
    @27
    @20
    @29
    @23
    @16
    wph
    @1
    @12
    @15
    eleq1
    anbi2d
    @29
    @2
    @17
    @26
    @19
    @1
    @12
    cF
    fveq2
    @29
    @25
    @18
    cF
    @1
    @12
    c1
    caddc
    oveq1
    fveq2d
    sseq12d
    imbi12d
    iunincfi.2
    chvarv
    syl2anc
    ssinc
    3adant3
    wph
    @10
    @8
    simp3
    sseldd
    3exp
    rexlimdv
    imp
    syldan
    ralrimiva
    vx
    @3
    @4
    dfss3
    sylibr
    wph
    cN
    @0
    wcel
    #
    @4
    @3
    wss
    wph
    cN
    @22
    wcel
    @30
    iunincfi.1
    cM
    cN
    eluzfz2
    syl
    vn
    @0
    @2
    cN
    @4
    @1
    cN
    cF
    fveq2
    ssiun2s
    syl
    eqssd
end
