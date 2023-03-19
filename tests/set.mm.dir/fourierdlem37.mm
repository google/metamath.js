include "cr.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "clt.mm"
include "csup.mm"
include "wi.mm"
include "wa.mm"
include "ssrab2.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "ltso.mm"
include "a1i.mm"
include "cfz.mm"
include "fzfi.mm"
include "fzossfz.mm"
include "sstri.mm"
include "ssfi.mm"
include "mp2an.mm"
include "cz.mm"
include "0zd.mm"
include "nnzd.mm"
include "nngt0d.mm"
include "fzolb.mm"
include "syl3anbrc.mm"
include "adantr.mm"
include "wceq.mm"
include "cif.mm"
include "c1.mm"
include "caddc.mm"
include "wral.mm"
include "cmap.mm"
include "cn.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "simplld.mm"
include "fourierdlem11.mm"
include "simp1d.mm"
include "eqeltrd.mm"
include "eqled.mm"
include "ad2antrr.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "wn.mm"
include "cioc.mm"
include "cxr.mm"
include "rexrd.mm"
include "simp2d.mm"
include "iocssre.mm"
include "syl2anc.mm"
include "simp3d.mm"
include "fourierdlem4.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "w3a.mm"
include "elioc2.mm"
include "eqbrtrd.mm"
include "ltled.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "cmpt.mm"
include "eqeq1.mm"
include "id.mm"
include "ifbieq2d.mm"
include "ifcld.mm"
include "fvmptd.mm"
include "breqtrrd.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "fzssz.mm"
include "zssre.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldi.mm"
include "fmptd.mm"
include "ex.mm"
include "jca.mm"

theorem fourierdlem37
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vi: setvar i
  let vm: setvar m
  let cE: class E
  let cI: class I
  let cL: class L
  let cM: class M
  let vp: setvar p
  let vk: setvar k
  assume fourierdlem37.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem37.m: |- ( ph -> M e. NN )
  assume fourierdlem37.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem37.t: |- T = ( B - A )
  assume fourierdlem37.e: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )
  assume fourierdlem37.l: |- L = ( y e. ( A (,] B ) |-> if ( y = B , A , y ) )
  assume fourierdlem37.i: |- I = ( x e. RR |-> sup ( { i e. ( 0 ..^ M ) | ( Q ` i ) <_ ( L ` ( E ` x ) ) } , RR , < ) )

  disjoint A m
  disjoint A p
  disjoint m p
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B m
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint E i
  disjoint E y
  disjoint L i
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint i m
  disjoint i p
  disjoint M x
  disjoint i x
  disjoint Q i
  disjoint Q p
  disjoint T x
  disjoint i ph
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( I : RR --> ( 0 ..^ M ) /\ ( x e. RR -> sup ( { i e. ( 0 ..^ M ) | ( Q ` i ) <_ ( L ` ( E ` x ) ) } , RR , < ) e. { i e. ( 0 ..^ M ) | ( Q ` i ) <_ ( L ` ( E ` x ) ) } ) ) )

  proof
    wph
    cr
    cc0
    cM
    cfzo
    co
    #
    cI
    wf
    vx
    cv
    #
    cr
    wcel
    #
    vi
    cv
    #
    cQ
    cfv
    #
    @1
    cE
    cfv
    #
    cL
    cfv
    #
    cle
    wbr
    #
    vi
    @0
    crab
    #
    cr
    clt
    csup
    #
    @8
    wcel
    #
    wi
    wph
    vx
    cr
    @9
    @0
    cI
    wph
    @2
    wa
    #
    @8
    @0
    @9
    @7
    vi
    @0
    ssrab2
    #
    @11
    cr
    clt
    wor
    #
    @8
    cfn
    wcel
    #
    @8
    c0
    wne
    #
    @8
    cr
    wss
    #
    @10
    @13
    @11
    ltso
    a1i
    @14
    @11
    cc0
    cM
    cfz
    co
    #
    cfn
    wcel
    @8
    @17
    wss
    @14
    cc0
    cM
    fzfi
    @8
    @0
    @17
    @12
    cc0
    cM
    fzossfz
    #
    sstri
    @17
    @8
    ssfi
    mp2an
    a1i
    @11
    cc0
    @8
    wcel
    #
    @15
    @11
    cc0
    @0
    wcel
    #
    cc0
    cQ
    cfv
    #
    @6
    cle
    wbr
    #
    @19
    wph
    @20
    @2
    wph
    cc0
    cz
    wcel
    cM
    cz
    wcel
    cc0
    cM
    clt
    wbr
    @20
    wph
    0zd
    wph
    cM
    fourierdlem37.m
    nnzd
    wph
    cM
    fourierdlem37.m
    nngt0d
    cc0
    cM
    fzolb
    syl3anbrc
    adantr
    @11
    @21
    @5
    cB
    wceq
    #
    cA
    @5
    cif
    #
    @6
    cle
    @11
    @23
    @21
    @24
    cle
    wbr
    @11
    @23
    wa
    @21
    cA
    @24
    cle
    wph
    @21
    cA
    cle
    wbr
    @2
    @23
    wph
    @21
    cA
    wph
    @21
    cA
    cr
    wph
    @21
    cA
    wceq
    #
    cM
    cQ
    cfv
    cB
    wceq
    #
    @4
    @3
    c1
    caddc
    co
    cQ
    cfv
    clt
    wbr
    vi
    @0
    wral
    #
    wph
    cQ
    cr
    @17
    cmap
    co
    wcel
    #
    @25
    @26
    wa
    @27
    wa
    #
    wph
    cQ
    cM
    cP
    cfv
    wcel
    #
    @28
    @29
    wa
    #
    fourierdlem37.q
    wph
    cM
    cn
    wcel
    @30
    @31
    wb
    fourierdlem37.m
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem37.p
    fourierdlem2
    syl
    mpbid
    simprd
    simplld
    #
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    wph
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem37.p
    fourierdlem37.m
    fourierdlem37.q
    fourierdlem11
    #
    simp1d
    #
    eqeltrd
    #
    @32
    eqled
    ad2antrr
    @23
    cA
    @24
    wceq
    @11
    @23
    @24
    cA
    @23
    cA
    @5
    iftrue
    eqcomd
    adantl
    breqtrd
    @11
    @23
    wn
    #
    wa
    @21
    @5
    @24
    cle
    @11
    @21
    @5
    cle
    wbr
    @39
    @11
    @21
    @5
    wph
    @21
    cr
    wcel
    @2
    @38
    adantr
    @11
    cA
    cB
    cioc
    co
    #
    cr
    @5
    @11
    cA
    cxr
    wcel
    #
    @34
    @40
    cr
    wss
    @11
    cA
    wph
    @33
    @2
    @37
    adantr
    #
    rexrd
    #
    wph
    @34
    @2
    wph
    @33
    @34
    @35
    @36
    simp2d
    #
    adantr
    #
    cA
    cB
    iocssre
    syl2anc
    wph
    cr
    @40
    @1
    cE
    wph
    vx
    cA
    cB
    cT
    cE
    @37
    @44
    wph
    @33
    @34
    @35
    @36
    simp3d
    fourierdlem37.t
    fourierdlem37.e
    fourierdlem4
    ffvelrnda
    #
    sseldd
    #
    @11
    @21
    cA
    @5
    clt
    wph
    @25
    @2
    @32
    adantr
    @11
    @5
    cr
    wcel
    #
    cA
    @5
    clt
    wbr
    #
    @5
    cB
    cle
    wbr
    #
    @11
    @5
    @40
    wcel
    #
    @48
    @49
    @50
    w3a
    #
    @46
    @11
    @41
    @34
    @51
    @52
    wb
    @43
    @45
    cA
    cB
    @5
    elioc2
    syl2anc
    mpbid
    simp2d
    eqbrtrd
    ltled
    adantr
    @39
    @5
    @24
    wceq
    @11
    @39
    @24
    @5
    @23
    cA
    @5
    iffalse
    eqcomd
    adantl
    breqtrd
    pm2.61dan
    @11
    vy
    @5
    vy
    cv
    #
    cB
    wceq
    #
    cA
    @53
    cif
    #
    @24
    @40
    cL
    cr
    cL
    vy
    @40
    @55
    cmpt
    wceq
    @11
    fourierdlem37.l
    a1i
    @53
    @5
    wceq
    #
    @55
    @24
    wceq
    @11
    @56
    @54
    @23
    @53
    @5
    cA
    @53
    @5
    cB
    eqeq1
    @56
    id
    ifbieq2d
    adantl
    @46
    @11
    @23
    cA
    @5
    cr
    @42
    @47
    ifcld
    fvmptd
    breqtrrd
    @7
    @22
    vi
    cc0
    @0
    @3
    cc0
    wceq
    @4
    @21
    @6
    cle
    @3
    cc0
    cQ
    fveq2
    breq1d
    elrab
    sylanbrc
    @8
    cc0
    ne0i
    syl
    @16
    @11
    @8
    @0
    cr
    @12
    @0
    cz
    cr
    @0
    @17
    cz
    @18
    cc0
    cM
    fzssz
    sstri
    zssre
    sstri
    sstri
    a1i
    cr
    @8
    clt
    fisupcl
    syl13anc
    #
    sseldi
    fourierdlem37.i
    fmptd
    wph
    @2
    @10
    @57
    ex
    jca
end
