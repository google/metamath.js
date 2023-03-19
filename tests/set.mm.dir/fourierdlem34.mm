include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "cmap.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "cn.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "elmapi.mm"
include "wn.mm"
include "simplr.mm"
include "ffvelrnda.mm"
include "ad2antrr.mm"
include "ad4ant14.mm"
include "adantllr.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "simprrd.mm"
include "r19.21bi.mm"
include "chvarv.mm"
include "simpllr.mm"
include "simpr.mm"
include "monoords.mm"
include "ltned.mm"
include "neneqd.mm"
include "adantlr.mm"
include "simpll.mm"
include "elfzelz.mm"
include "zred.mm"
include "ad3antlr.mm"
include "ad4antlr.mm"
include "wne.mm"
include "neqne.mm"
include "necomd.mm"
include "ad2antlr.mm"
include "lttri5d.mm"
include "adantr.mm"
include "simp-4l.mm"
include "sylancom.mm"
include "gtned.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "condan.mm"
include "ex.mm"
include "ralrimiva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem fourierdlem34
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vi: setvar i
  let vm: setvar m
  let cM: class M
  let vp: setvar p
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem34.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem34.m: |- ( ph -> M e. NN )
  assume fourierdlem34.q: |- ( ph -> Q e. ( P ` M ) )

  disjoint A m
  disjoint A p
  disjoint m p
  disjoint B m
  disjoint B p
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint i m
  disjoint i p
  disjoint Q i
  disjoint Q p
  disjoint i ph
  disjoint M j
  disjoint M k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint Q j
  disjoint Q k
  disjoint j ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> Q : ( 0 ... M ) -1-1-> RR )

  proof
    wph
    cc0
    cM
    cfz
    co
    #
    cr
    cQ
    wf
    #
    vi
    cv
    #
    cQ
    cfv
    #
    vj
    cv
    #
    cQ
    cfv
    #
    wceq
    #
    @2
    @4
    wceq
    #
    wi
    #
    vj
    @0
    wral
    #
    vi
    @0
    wral
    @0
    cr
    cQ
    wf1
    wph
    cQ
    cr
    @0
    cmap
    co
    wcel
    #
    @1
    wph
    @10
    cc0
    cQ
    cfv
    cA
    wceq
    cM
    cQ
    cfv
    cB
    wceq
    wa
    #
    @3
    @2
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    #
    wa
    #
    wph
    cQ
    cM
    cP
    cfv
    wcel
    #
    @10
    @17
    wa
    #
    fourierdlem34.q
    wph
    cM
    cn
    wcel
    @18
    @19
    wb
    fourierdlem34.m
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem34.p
    fourierdlem2
    syl
    mpbid
    #
    simpld
    cQ
    cr
    @0
    elmapi
    syl
    #
    wph
    @9
    vi
    @0
    wph
    @2
    @0
    wcel
    #
    wa
    #
    @8
    vj
    @0
    @23
    @4
    @0
    wcel
    #
    wa
    #
    @6
    @7
    @25
    @6
    wa
    @7
    @6
    @25
    @6
    @7
    wn
    #
    simplr
    @25
    @26
    @6
    wn
    #
    @6
    @25
    @26
    wa
    #
    @2
    @4
    clt
    wbr
    #
    @27
    @25
    @29
    @27
    @26
    @25
    @29
    wa
    #
    @3
    @5
    @30
    @3
    @5
    @23
    @3
    cr
    wcel
    @24
    @29
    wph
    @0
    cr
    @2
    cQ
    @21
    ffvelrnda
    ad2antrr
    @30
    vk
    cQ
    @2
    @4
    cc0
    cM
    @23
    @29
    vk
    cv
    #
    @0
    wcel
    #
    @31
    cQ
    cfv
    #
    cr
    wcel
    #
    @24
    wph
    @32
    @34
    @22
    @29
    wph
    @0
    cr
    @31
    cQ
    @21
    ffvelrnda
    #
    ad4ant14
    adantllr
    @23
    @29
    @31
    @15
    wcel
    #
    @33
    @31
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    clt
    wbr
    #
    @24
    wph
    @36
    @39
    @22
    @29
    wph
    @2
    @15
    wcel
    #
    wa
    #
    @14
    wi
    wph
    @36
    wa
    #
    @39
    wi
    vi
    vk
    @2
    @31
    wceq
    #
    @41
    @42
    @14
    @39
    @43
    @40
    @36
    wph
    @2
    @31
    @15
    eleq1
    anbi2d
    @43
    @3
    @33
    @13
    @38
    clt
    @2
    @31
    cQ
    fveq2
    @43
    @12
    @37
    cQ
    @2
    @31
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    imbi12d
    wph
    @14
    vi
    @15
    wph
    @10
    @11
    @16
    @20
    simprrd
    r19.21bi
    chvarv
    #
    ad4ant14
    adantllr
    wph
    @22
    @24
    @29
    simpllr
    @23
    @24
    @29
    simplr
    @25
    @29
    simpr
    monoords
    ltned
    neneqd
    adantlr
    @28
    @29
    wn
    #
    wa
    #
    @25
    @4
    @2
    clt
    wbr
    #
    @27
    @25
    @26
    @45
    simpll
    @46
    @4
    @2
    @24
    @4
    cr
    wcel
    @23
    @26
    @45
    @24
    @4
    @4
    cc0
    cM
    elfzelz
    zred
    ad3antlr
    @22
    @2
    cr
    wcel
    wph
    @24
    @26
    @45
    @22
    @2
    @2
    cc0
    cM
    elfzelz
    zred
    ad4antlr
    @26
    @4
    @2
    wne
    @25
    @45
    @26
    @2
    @4
    @2
    @4
    neqne
    necomd
    ad2antlr
    @28
    @45
    simpr
    lttri5d
    @25
    @47
    wa
    #
    @3
    @5
    @48
    @5
    @3
    wph
    @24
    @47
    @5
    cr
    wcel
    #
    @22
    wph
    @24
    wa
    @49
    @47
    wph
    @0
    cr
    @4
    cQ
    @21
    ffvelrnda
    adantr
    adantllr
    @48
    vk
    cQ
    @4
    @2
    cc0
    cM
    @48
    @32
    wph
    @34
    wph
    @22
    @24
    @47
    @32
    simp-4l
    @35
    sylancom
    @48
    @36
    wph
    @39
    wph
    @22
    @24
    @47
    @36
    simp-4l
    @44
    sylancom
    @23
    @24
    @47
    simplr
    wph
    @22
    @24
    @47
    simpllr
    @25
    @47
    simpr
    monoords
    gtned
    neneqd
    syl2anc
    pm2.61dan
    adantlr
    condan
    ex
    ralrimiva
    ralrimiva
    vi
    vj
    @0
    cr
    cQ
    dff13
    sylanbrc
end
