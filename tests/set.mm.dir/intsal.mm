include "cint.mm"
include "csalg.mm"
include "wcel.mm"
include "c0.mm"
include "cuni.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "w3a.mm"
include "wa.mm"
include "simpl.mm"
include "sselda.mm"
include "simpr.mm"
include "0sal.mm"
include "syl.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "0ex.mm"
include "elint2.mm"
include "sylibr.mm"
include "wceq.mm"
include "intsaluni.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eqtr2d.mm"
include "difeq1d.mm"
include "adantlr.mm"
include "elinti.mm"
include "imp.mm"
include "adantll.mm"
include "saldifcl.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "wne.mm"
include "intex.mm"
include "biimpi.mm"
include "uniexg.mm"
include "difexg.mm"
include "elintg.mm"
include "mpbird.mm"
include "ad4ant14.mm"
include "wss.mm"
include "elpwi.mm"
include "intss1.mm"
include "adantl.mm"
include "sstrd.mm"
include "vex.mm"
include "elpw.mm"
include "simplr.mm"
include "salunicl.mm"
include "vuniex.mm"
include "a1i.mm"
include "ex.mm"
include "3jca.mm"
include "issal.mm"

theorem intsal
  let wph: wff ph
  let cG: class G
  let cX: class X
  let vs: setvar s
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  assume intsal.ga: |- ( ph -> G C_ SAlg )
  assume intsal.gn0: |- ( ph -> G =/= (/) )
  assume intsal.x: |- ( ( ph /\ s e. G ) -> U. s = X )

  disjoint G s
  disjoint X s
  disjoint ph s
  disjoint G y
  disjoint s y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> |^| G e. SAlg )

  proof
    wph
    cG
    cint
    #
    csalg
    wcel
    #
    c0
    @0
    wcel
    #
    @0
    cuni
    #
    vy
    cv
    #
    cdif
    #
    @0
    wcel
    #
    vy
    @0
    wral
    #
    @4
    com
    cdom
    wbr
    #
    @4
    cuni
    #
    @0
    wcel
    #
    wi
    #
    vy
    @0
    cpw
    #
    wral
    #
    w3a
    #
    wph
    @2
    @7
    @13
    wph
    c0
    vs
    cv
    #
    wcel
    #
    vs
    cG
    wral
    @2
    wph
    @16
    vs
    cG
    wph
    @15
    cG
    wcel
    #
    wa
    #
    wph
    @15
    csalg
    wcel
    #
    @16
    wph
    @17
    simpl
    wph
    cG
    csalg
    @15
    intsal.ga
    sselda
    #
    wph
    @19
    wa
    @19
    @16
    wph
    @19
    simpr
    @15
    0sal
    syl
    syl2anc
    ralrimiva
    vs
    c0
    cG
    0ex
    elint2
    sylibr
    wph
    @6
    vy
    @0
    wph
    @4
    @0
    wcel
    #
    wa
    #
    @6
    @5
    @15
    wcel
    #
    vs
    cG
    wral
    #
    @22
    @23
    vs
    cG
    @22
    @17
    wa
    #
    @5
    @15
    cuni
    #
    @4
    cdif
    #
    @15
    wph
    @17
    @5
    @27
    wceq
    @21
    @18
    @3
    @26
    @4
    @18
    @26
    cX
    @3
    intsal.x
    wph
    cX
    @3
    wceq
    @17
    wph
    @3
    cX
    wph
    cG
    cX
    vs
    intsal.ga
    intsal.gn0
    intsal.x
    intsaluni
    eqcomd
    adantr
    eqtr2d
    difeq1d
    adantlr
    @25
    @19
    @4
    @15
    wcel
    #
    @27
    @15
    wcel
    wph
    @17
    @19
    @21
    @20
    adantlr
    @21
    @17
    @28
    wph
    @21
    @17
    @28
    @4
    cG
    @15
    elinti
    imp
    adantll
    @15
    @4
    saldifcl
    syl2anc
    eqeltrd
    ralrimiva
    @22
    @5
    cvv
    wcel
    #
    @6
    @24
    wb
    wph
    @29
    @21
    wph
    @3
    cvv
    wcel
    #
    @29
    wph
    @0
    cvv
    wcel
    #
    @30
    wph
    cG
    c0
    wne
    #
    @31
    intsal.gn0
    @32
    @31
    cG
    intex
    biimpi
    syl
    #
    @0
    cvv
    uniexg
    syl
    @3
    @4
    cvv
    difexg
    syl
    adantr
    vs
    @5
    cG
    cvv
    elintg
    syl
    mpbird
    ralrimiva
    wph
    @11
    vy
    @12
    wph
    @4
    @12
    wcel
    #
    wa
    #
    @8
    @10
    @35
    @8
    wa
    #
    @10
    @9
    @15
    wcel
    #
    vs
    cG
    wral
    #
    @36
    @37
    vs
    cG
    @36
    @17
    wa
    @15
    @4
    wph
    @17
    @19
    @34
    @8
    @20
    ad4ant14
    @35
    @17
    @4
    @15
    cpw
    wcel
    #
    @8
    @34
    @17
    @39
    wph
    @34
    @17
    wa
    #
    @4
    @15
    wss
    @39
    @40
    @4
    @0
    @15
    @34
    @4
    @0
    wss
    @17
    @4
    @0
    elpwi
    adantr
    @17
    @0
    @15
    wss
    @34
    @15
    cG
    intss1
    adantl
    sstrd
    @4
    @15
    vy
    vex
    elpw
    sylibr
    adantll
    adantlr
    @35
    @8
    @17
    simplr
    salunicl
    ralrimiva
    @36
    @9
    cvv
    wcel
    #
    @10
    @38
    wb
    @41
    @36
    vy
    vuniex
    a1i
    vs
    @9
    cG
    cvv
    elintg
    syl
    mpbird
    ex
    ralrimiva
    3jca
    wph
    @31
    @1
    @14
    wb
    @33
    vy
    @0
    cvv
    issal
    syl
    mpbird
end
