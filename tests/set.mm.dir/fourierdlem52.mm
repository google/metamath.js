include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cicc.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "clt.mm"
include "wiso.mm"
include "wf1o.mm"
include "cr.mm"
include "iccssred.mm"
include "sstrd.mm"
include "fourierdlem36.mm"
include "isof1o.mm"
include "f1of.mm"
include "3syl.mm"
include "fssd.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wfo.mm"
include "wcel.mm"
include "f1ofo.mm"
include "foelrn.mm"
include "syl2anc.mm"
include "w3a.mm"
include "wa.mm"
include "elfzle1.mm"
include "adantl.mm"
include "cxr.mm"
include "wss.mm"
include "wb.mm"
include "adantr.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "cz.mm"
include "fzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "jctil.mm"
include "cuz.mm"
include "cn0.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "cn.mm"
include "cfn.mm"
include "hashcl.mm"
include "syl.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "hashge1.mm"
include "elnnnn0c.mm"
include "sylanbrc.mm"
include "nnm1nn0.mm"
include "syl5eqel.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "anim1i.mm"
include "leisorel.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "3adant3.mm"
include "eqcom.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "breqtrd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "rexrd.mm"
include "ffvelrnd.mm"
include "iccgelb.mm"
include "sseldd.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "eluzfz2.mm"
include "iccleub.mm"
include "simp3.mm"
include "elfzle2.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "syl112anc.mm"
include "eqbrtrd.mm"
include "jca31.mm"

theorem fourierdlem52
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem52.tf: |- ( ph -> T e. Fin )
  assume fourierdlem52.n: |- N = ( ( # ` T ) - 1 )
  assume fourierdlem52.s: |- S = ( iota f f Isom < , < ( ( 0 ... N ) , T ) )
  assume fourierdlem52.a: |- ( ph -> A e. RR )
  assume fourierdlem52.b: |- ( ph -> B e. RR )
  assume fourierdlem52.t: |- ( ph -> T C_ ( A [,] B ) )
  assume fourierdlem52.at: |- ( ph -> A e. T )
  assume fourierdlem52.bt: |- ( ph -> B e. T )

  disjoint N f
  disjoint S f
  disjoint T f
  disjoint f ph
  disjoint A j
  disjoint B j
  disjoint N j
  disjoint S j
  disjoint T j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( ( S : ( 0 ... N ) --> ( A [,] B ) /\ ( S ` 0 ) = A ) /\ ( S ` N ) = B ) )

  proof
    wph
    cc0
    cN
    cfz
    co
    #
    cA
    cB
    cicc
    co
    #
    cS
    wf
    cc0
    cS
    cfv
    #
    cA
    wceq
    #
    cN
    cS
    cfv
    #
    cB
    wceq
    #
    wph
    @0
    cT
    @1
    cS
    wph
    @0
    cT
    clt
    clt
    cS
    wiso
    #
    @0
    cT
    cS
    wf1o
    #
    @0
    cT
    cS
    wf
    wph
    cT
    vf
    cS
    cN
    fourierdlem52.tf
    wph
    cT
    @1
    cr
    fourierdlem52.t
    wph
    cA
    cB
    fourierdlem52.a
    fourierdlem52.b
    iccssred
    #
    sstrd
    #
    fourierdlem52.s
    fourierdlem52.n
    fourierdlem36
    #
    @0
    cT
    clt
    clt
    cS
    isof1o
    #
    @0
    cT
    cS
    f1of
    3syl
    fourierdlem52.t
    fssd
    #
    wph
    @3
    @2
    cA
    cle
    wbr
    #
    cA
    @2
    cle
    wbr
    #
    wph
    cA
    vj
    cv
    #
    cS
    cfv
    #
    wceq
    #
    vj
    @0
    wrex
    #
    @13
    wph
    @0
    cT
    cS
    wfo
    #
    cA
    cT
    wcel
    #
    @18
    wph
    @6
    @7
    @19
    @10
    @11
    @0
    cT
    cS
    f1ofo
    3syl
    #
    fourierdlem52.at
    vj
    @0
    cT
    cA
    cS
    foelrn
    syl2anc
    wph
    @17
    @13
    vj
    @0
    wph
    @15
    @0
    wcel
    #
    @17
    w3a
    @2
    @16
    cA
    cle
    wph
    @22
    @2
    @16
    cle
    wbr
    #
    @17
    wph
    @22
    wa
    #
    cc0
    @15
    cle
    wbr
    #
    @23
    @22
    @25
    wph
    @15
    cc0
    cN
    elfzle1
    adantl
    @24
    @6
    @0
    cxr
    wss
    #
    cT
    cxr
    wss
    #
    wa
    #
    cc0
    @0
    wcel
    #
    @22
    wa
    @25
    @23
    wb
    wph
    @6
    @22
    @10
    adantr
    @24
    @27
    @26
    wph
    @27
    @22
    wph
    cT
    cr
    cxr
    @9
    ressxr
    syl6ss
    adantr
    @0
    cz
    cxr
    cc0
    cN
    fzssz
    cz
    cr
    cxr
    zssre
    ressxr
    sstri
    sstri
    jctil
    #
    wph
    @29
    @22
    wph
    cN
    cc0
    cuz
    cfv
    #
    wcel
    #
    @29
    wph
    cN
    cn0
    @31
    wph
    cN
    cT
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cn0
    fourierdlem52.n
    wph
    @33
    cn
    wcel
    #
    @34
    cn0
    wcel
    wph
    @33
    cn0
    wcel
    #
    c1
    @33
    cle
    wbr
    #
    @35
    wph
    cT
    cfn
    wcel
    #
    @36
    fourierdlem52.tf
    cT
    hashcl
    syl
    wph
    @38
    cT
    c0
    wne
    #
    @37
    fourierdlem52.tf
    wph
    @20
    @39
    fourierdlem52.at
    cT
    cA
    ne0i
    syl
    cT
    cfn
    hashge1
    syl2anc
    @33
    elnnnn0c
    sylanbrc
    @33
    nnm1nn0
    syl
    syl5eqel
    nn0uz
    syl6eleq
    #
    cc0
    cN
    eluzfz1
    syl
    #
    anim1i
    @0
    cT
    cc0
    @15
    cS
    leisorel
    syl3anc
    mpbid
    3adant3
    @17
    wph
    @16
    cA
    wceq
    #
    @22
    @17
    @42
    cA
    @16
    eqcom
    biimpi
    3ad2ant3
    breqtrd
    rexlimdv3a
    mpd
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @2
    @1
    wcel
    @14
    wph
    cA
    fourierdlem52.a
    rexrd
    #
    wph
    cB
    fourierdlem52.b
    rexrd
    #
    wph
    @0
    @1
    cc0
    cS
    @12
    @41
    ffvelrnd
    #
    cA
    cB
    @2
    iccgelb
    syl3anc
    wph
    @2
    cA
    wph
    @1
    cr
    @2
    @8
    @47
    sseldd
    fourierdlem52.a
    letri3d
    mpbir2and
    wph
    @5
    @4
    cB
    cle
    wbr
    #
    cB
    @4
    cle
    wbr
    #
    wph
    @43
    @44
    @4
    @1
    wcel
    @48
    @45
    @46
    wph
    @0
    @1
    cN
    cS
    @12
    wph
    @32
    cN
    @0
    wcel
    #
    @40
    cc0
    cN
    eluzfz2
    syl
    #
    ffvelrnd
    #
    cA
    cB
    @4
    iccleub
    syl3anc
    wph
    cB
    @16
    wceq
    #
    vj
    @0
    wrex
    #
    @49
    wph
    @19
    cB
    cT
    wcel
    @54
    @21
    fourierdlem52.bt
    vj
    @0
    cT
    cB
    cS
    foelrn
    syl2anc
    wph
    @53
    @49
    vj
    @0
    wph
    @22
    @53
    w3a
    #
    cB
    @16
    @4
    cle
    wph
    @22
    @53
    simp3
    @55
    @15
    cN
    cle
    wbr
    #
    @16
    @4
    cle
    wbr
    #
    @22
    wph
    @56
    @53
    @15
    cc0
    cN
    elfzle2
    3ad2ant2
    @55
    @6
    @28
    @22
    @50
    @56
    @57
    wb
    wph
    @22
    @6
    @53
    @10
    3ad2ant1
    wph
    @22
    @28
    @53
    @30
    3adant3
    wph
    @22
    @53
    simp2
    wph
    @22
    @50
    @53
    @51
    3ad2ant1
    @0
    cT
    @15
    cN
    cS
    leisorel
    syl112anc
    mpbid
    eqbrtrd
    rexlimdv3a
    mpd
    wph
    @4
    cB
    wph
    @1
    cr
    @4
    @8
    @52
    sseldd
    fourierdlem52.b
    letri3d
    mpbir2and
    jca31
end
