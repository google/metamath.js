include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wral.mm"
include "cfz.mm"
include "cmap.mm"
include "cn.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "simpld.mm"
include "wf.mm"
include "elmapi.mm"
include "cle.mm"
include "0red.mm"
include "leidd.mm"
include "nnred.mm"
include "nngt0d.mm"
include "ltled.mm"
include "cz.mm"
include "0zd.mm"
include "nnzd.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "0le1.mm"
include "a1i.mm"
include "nnge1d.mm"
include "1zzd.mm"
include "elfzo.mm"
include "wi.mm"
include "0re.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "r19.21bi.mm"
include "vtoclg.mm"
include "ax-mp.mm"
include "mpdan.mm"
include "0p1e1.mm"
include "3brtr3d.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "adantr.mm"
include "elfzelz.mm"
include "zred.mm"
include "1red.mm"
include "0lt1.mm"
include "elfzle1.mm"
include "ltletrd.mm"
include "elfzle2.mm"
include "elfzel2.mm"
include "adantl.mm"
include "cmin.mm"
include "peano2rem.mm"
include "ltm1d.mm"
include "lelttrd.mm"
include "peano2re.mm"
include "ltp1d.mm"
include "lttrd.mm"
include "leadd1dd.mm"
include "nncnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "breqtrd.mm"
include "peano2zd.mm"
include "syldan.mm"
include "monoord.mm"
include "3jca.mm"

theorem fourierdlem11
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vi: setvar i
  let vm: setvar m
  let cM: class M
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem11.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem11.m: |- ( ph -> M e. NN )
  assume fourierdlem11.q: |- ( ph -> Q e. ( P ` M ) )

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
  disjoint k x
  assert |- ( ph -> ( A e. RR /\ B e. RR /\ A < B ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    clt
    wbr
    wph
    cc0
    cQ
    cfv
    #
    cA
    cr
    wph
    @0
    cA
    wceq
    #
    cM
    cQ
    cfv
    #
    cB
    wceq
    #
    wph
    @1
    @3
    wa
    #
    vi
    cv
    #
    cQ
    cfv
    #
    @5
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
    wph
    cQ
    cr
    cc0
    cM
    cfz
    co
    #
    cmap
    co
    wcel
    #
    @4
    @11
    wa
    #
    wph
    cQ
    cM
    cP
    cfv
    wcel
    #
    @13
    @14
    wa
    #
    fourierdlem11.q
    wph
    cM
    cn
    wcel
    @15
    @16
    wb
    fourierdlem11.m
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem11.p
    fourierdlem2
    syl
    mpbid
    #
    simprd
    #
    simpld
    #
    simpld
    #
    wph
    @12
    cr
    cc0
    cQ
    wph
    @13
    @12
    cr
    cQ
    wf
    #
    wph
    @13
    @14
    @17
    simpld
    cQ
    cr
    @12
    elmapi
    syl
    #
    wph
    cc0
    @12
    wcel
    #
    cc0
    cc0
    cle
    wbr
    #
    cc0
    cM
    cle
    wbr
    #
    wph
    cc0
    wph
    0red
    #
    leidd
    #
    wph
    cc0
    cM
    @26
    wph
    cM
    fourierdlem11.m
    nnred
    #
    wph
    cM
    fourierdlem11.m
    nngt0d
    #
    ltled
    #
    wph
    cc0
    cz
    wcel
    #
    @31
    cM
    cz
    wcel
    #
    @23
    @24
    @25
    wa
    wb
    wph
    0zd
    #
    @33
    wph
    cM
    fourierdlem11.m
    nnzd
    #
    cc0
    cc0
    cM
    elfz
    syl3anc
    mpbir2and
    ffvelrnd
    eqeltrrd
    #
    wph
    @2
    cB
    cr
    wph
    @1
    @3
    @19
    simprd
    #
    wph
    @12
    cr
    cM
    cQ
    @22
    wph
    cM
    @12
    wcel
    #
    @25
    cM
    cM
    cle
    wbr
    #
    @30
    wph
    cM
    @28
    leidd
    wph
    @32
    @31
    @32
    @37
    @25
    @38
    wa
    wb
    @34
    @33
    @34
    cM
    cc0
    cM
    elfz
    syl3anc
    mpbir2and
    ffvelrnd
    eqeltrrd
    #
    wph
    cA
    c1
    cQ
    cfv
    #
    cB
    @35
    wph
    @12
    cr
    c1
    cQ
    @22
    wph
    c1
    @12
    wcel
    #
    cc0
    c1
    cle
    wbr
    #
    c1
    cM
    cle
    wbr
    #
    @42
    wph
    0le1
    a1i
    wph
    cM
    fourierdlem11.m
    nnge1d
    wph
    c1
    cz
    wcel
    @31
    @32
    @41
    @42
    @43
    wa
    wb
    wph
    1zzd
    @33
    @34
    c1
    cc0
    cM
    elfz
    syl3anc
    mpbir2and
    ffvelrnd
    @39
    wph
    @0
    cc0
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cA
    @40
    clt
    wph
    cc0
    @10
    wcel
    #
    @0
    @45
    clt
    wbr
    #
    wph
    @46
    @24
    cc0
    cM
    clt
    wbr
    #
    @27
    @29
    wph
    @31
    @31
    @32
    @46
    @24
    @48
    wa
    wb
    @33
    @33
    @34
    cc0
    cc0
    cM
    elfzo
    syl3anc
    mpbir2and
    cc0
    cr
    wcel
    wph
    @46
    wa
    #
    @47
    wi
    #
    0re
    wph
    @5
    @10
    wcel
    #
    wa
    #
    @9
    wi
    @50
    vi
    cc0
    cr
    @5
    cc0
    wceq
    #
    @52
    @49
    @9
    @47
    @53
    @51
    @46
    wph
    @5
    cc0
    @10
    eleq1
    anbi2d
    @53
    @6
    @0
    @8
    @45
    clt
    @5
    cc0
    cQ
    fveq2
    @53
    @7
    @44
    cQ
    @5
    cc0
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    imbi12d
    wph
    @9
    vi
    @10
    wph
    @4
    @11
    @18
    simprd
    r19.21bi
    #
    vtoclg
    ax-mp
    mpdan
    @20
    wph
    @44
    c1
    cQ
    @44
    c1
    wceq
    wph
    0p1e1
    a1i
    fveq2d
    3brtr3d
    wph
    @40
    @2
    cB
    cle
    wph
    vi
    cQ
    c1
    cM
    wph
    cM
    cn
    c1
    cuz
    cfv
    fourierdlem11.m
    nnuz
    syl6eleq
    wph
    @5
    c1
    cM
    cfz
    co
    wcel
    #
    wa
    @12
    cr
    @5
    cQ
    wph
    @21
    @55
    @22
    adantr
    @55
    @5
    @12
    wcel
    #
    wph
    @55
    @56
    cc0
    @5
    cle
    wbr
    #
    @5
    cM
    cle
    wbr
    #
    @55
    cc0
    @5
    @55
    0red
    #
    @55
    @5
    @5
    c1
    cM
    elfzelz
    #
    zred
    #
    @55
    cc0
    c1
    @5
    @59
    @55
    1red
    @61
    cc0
    c1
    clt
    wbr
    #
    @55
    0lt1
    a1i
    @5
    c1
    cM
    elfzle1
    ltletrd
    ltled
    @5
    c1
    cM
    elfzle2
    @55
    @5
    cz
    wcel
    #
    @31
    @32
    @56
    @57
    @58
    wa
    wb
    #
    @60
    @55
    0zd
    @5
    c1
    cM
    elfzel2
    @5
    cc0
    cM
    elfz
    #
    syl3anc
    mpbir2and
    adantl
    ffvelrnd
    wph
    @5
    c1
    cM
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    @6
    @8
    @68
    @12
    cr
    @5
    cQ
    wph
    @21
    @67
    @22
    adantr
    #
    @68
    @56
    @57
    @58
    @67
    @57
    wph
    @67
    cc0
    @5
    @67
    0red
    #
    @67
    @5
    @5
    c1
    @66
    elfzelz
    #
    zred
    #
    @67
    cc0
    c1
    @5
    @70
    @67
    1red
    #
    @72
    @62
    @67
    0lt1
    a1i
    @5
    c1
    @66
    elfzle1
    #
    ltletrd
    ltled
    adantl
    #
    @68
    @5
    cM
    @67
    @5
    cr
    wcel
    #
    wph
    @72
    adantl
    #
    wph
    cM
    cr
    wcel
    #
    @67
    @28
    adantr
    #
    @68
    @5
    @66
    cM
    @77
    @68
    @78
    @66
    cr
    wcel
    @79
    cM
    peano2rem
    syl
    #
    @79
    @67
    @5
    @66
    cle
    wbr
    wph
    @5
    c1
    @66
    elfzle2
    adantl
    #
    @68
    cM
    @79
    ltm1d
    lelttrd
    #
    ltled
    @68
    @63
    @31
    @32
    @64
    @67
    @63
    wph
    @71
    adantl
    #
    @68
    0zd
    #
    wph
    @32
    @67
    @34
    adantr
    #
    @65
    syl3anc
    mpbir2and
    ffvelrnd
    @68
    @12
    cr
    @7
    cQ
    @69
    @68
    @7
    @12
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @7
    cM
    cle
    wbr
    #
    @68
    cc0
    @7
    @68
    0red
    #
    @68
    @76
    @7
    cr
    wcel
    #
    @77
    @5
    peano2re
    #
    syl
    #
    @68
    cc0
    c1
    @7
    @89
    @68
    1red
    #
    @92
    @62
    @68
    0lt1
    a1i
    @67
    c1
    @7
    clt
    wbr
    wph
    @67
    c1
    @5
    @7
    @73
    @72
    @67
    @76
    @90
    @72
    @91
    syl
    @74
    @67
    @5
    @72
    ltp1d
    lelttrd
    adantl
    lttrd
    ltled
    @68
    @7
    @66
    c1
    caddc
    co
    #
    cM
    cle
    @68
    @5
    @66
    c1
    @77
    @80
    @93
    @81
    leadd1dd
    wph
    @94
    cM
    wceq
    @67
    wph
    cM
    c1
    wph
    cM
    fourierdlem11.m
    nncnd
    wph
    1cnd
    npcand
    adantr
    breqtrd
    @68
    @7
    cz
    wcel
    @31
    @32
    @86
    @87
    @88
    wa
    wb
    @68
    @5
    @83
    peano2zd
    @84
    @85
    @7
    cc0
    cM
    elfz
    syl3anc
    mpbir2and
    ffvelrnd
    wph
    @67
    @51
    @9
    @68
    @51
    @57
    @5
    cM
    clt
    wbr
    #
    @75
    @82
    @68
    @63
    @31
    @32
    @51
    @57
    @95
    wa
    wb
    @83
    @84
    @85
    @5
    cc0
    cM
    elfzo
    syl3anc
    mpbir2and
    @54
    syldan
    ltled
    monoord
    @36
    breqtrd
    ltletrd
    3jca
end
