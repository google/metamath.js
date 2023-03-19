include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "cun.mm"
include "cop.mm"
include "cin.mm"
include "c0.mm"
include "wlkf.mm"
include "wrdf.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "feq2i.mm"
include "sylib.mm"
include "3syl.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "snidg.mm"
include "syl.mm"
include "cedg.mm"
include "dmsnopg.mm"
include "eleqtrrd.mm"
include "fsnd.mm"
include "fzodisjsn.mm"
include "fun.mm"
include "syl21anc.mm"
include "wlkp1lem2.mm"
include "oveq2d.mm"
include "cuz.mm"
include "cn0.mm"
include "wlkcl.mm"
include "wi.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "elnn0uz.mm"
include "biimpi.mm"
include "syl6bi.mm"
include "ax-mp.mm"
include "fzosplitsn.mm"
include "eqtrd.mm"
include "dmeqd.mm"
include "dmun.mm"
include "syl6eq.mm"
include "feq123d.mm"
include "mpbird.mm"
include "iswrdb.mm"
include "sylibr.mm"
include "wlkp.mm"
include "ovexd.mm"
include "fzp1disj.mm"
include "fzsuc.mm"
include "unidm.mm"
include "feq23d.mm"
include "wlkp1lem8.mm"
include "w3a.mm"
include "wlkp1lem4.mm"
include "eqid.mm"
include "iswlk.mm"
include "mpbir3and.mm"

theorem wlkp1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume wlkp1.v: |- V = ( Vtx ` G )
  assume wlkp1.i: |- I = ( iEdg ` G )
  assume wlkp1.f: |- ( ph -> Fun I )
  assume wlkp1.a: |- ( ph -> I e. Fin )
  assume wlkp1.b: |- ( ph -> B e. _V )
  assume wlkp1.c: |- ( ph -> C e. V )
  assume wlkp1.d: |- ( ph -> -. B e. dom I )
  assume wlkp1.w: |- ( ph -> F ( Walks ` G ) P )
  assume wlkp1.n: |- N = ( # ` F )
  assume wlkp1.e: |- ( ph -> E e. ( Edg ` G ) )
  assume wlkp1.x: |- ( ph -> { ( P ` N ) , C } C_ E )
  assume wlkp1.u: |- ( ph -> ( iEdg ` S ) = ( I u. { <. B , E >. } ) )
  assume wlkp1.h: |- H = ( F u. { <. N , B >. } )
  assume wlkp1.q: |- Q = ( P u. { <. ( N + 1 ) , C >. } )
  assume wlkp1.s: |- ( ph -> ( Vtx ` S ) = V )
  assume wlkp1.l: |- ( ( ph /\ C = ( P ` N ) ) -> E = { C } )


  assert |- ( ph -> H ( Walks ` S ) Q )

  proof
    wph
    cH
    cQ
    cS
    cwlks
    cfv
    wbr
    #
    cH
    cS
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    #
    cc0
    cH
    chash
    cfv
    #
    cfz
    co
    #
    cS
    cvtx
    cfv
    #
    cQ
    wf
    #
    vk
    cv
    #
    cQ
    cfv
    #
    @8
    c1
    caddc
    co
    cQ
    cfv
    #
    wceq
    @8
    cH
    cfv
    @1
    cfv
    #
    @9
    csn
    wceq
    @9
    @10
    cpr
    @11
    wss
    wif
    vk
    cc0
    @4
    cfzo
    co
    #
    wral
    #
    wph
    @12
    @2
    cH
    wf
    #
    @3
    wph
    @14
    cc0
    cN
    cfzo
    co
    #
    cN
    csn
    #
    cun
    #
    cI
    cdm
    #
    cB
    cE
    cop
    csn
    #
    cdm
    #
    cun
    #
    cF
    cN
    cB
    cop
    csn
    #
    cun
    #
    wf
    #
    wph
    @15
    @18
    cF
    wf
    #
    @16
    @20
    @22
    wf
    @15
    @16
    cin
    c0
    wceq
    #
    @24
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    @18
    cword
    wcel
    #
    @25
    wlkp1.w
    cP
    cF
    cG
    cI
    wlkp1.i
    wlkf
    @28
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    @18
    cF
    wf
    @25
    @18
    cF
    wrdf
    @30
    @15
    @18
    cF
    @29
    cN
    cc0
    cfzo
    cN
    @29
    wlkp1.n
    eqcomi
    oveq2i
    feq2i
    sylib
    3syl
    wph
    cN
    cB
    cvv
    @20
    cN
    cvv
    wcel
    wph
    cN
    @29
    cvv
    wlkp1.n
    cF
    chash
    fvex
    eqeltri
    a1i
    wph
    cB
    cB
    csn
    #
    @20
    wph
    cB
    cvv
    wcel
    cB
    @31
    wcel
    wlkp1.b
    cB
    cvv
    snidg
    syl
    wph
    cE
    cG
    cedg
    cfv
    #
    wcel
    @20
    @31
    wceq
    wlkp1.e
    cB
    cE
    @32
    dmsnopg
    syl
    eleqtrrd
    fsnd
    @26
    wph
    cc0
    cN
    fzodisjsn
    a1i
    @15
    @16
    @18
    @20
    cF
    @22
    fun
    syl21anc
    wph
    @12
    @17
    @2
    @21
    cH
    @23
    cH
    @23
    wceq
    wph
    wlkp1.h
    a1i
    wph
    @12
    cc0
    cN
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @17
    wph
    @4
    @33
    cc0
    cfzo
    wph
    cB
    cC
    cP
    cS
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1lem2
    #
    oveq2d
    wph
    cN
    cc0
    cuz
    cfv
    wcel
    #
    @34
    @17
    wceq
    wph
    @27
    @29
    cn0
    wcel
    #
    @36
    wlkp1.w
    cP
    cF
    cG
    wlkcl
    cN
    @29
    wceq
    #
    @37
    @36
    wi
    wlkp1.n
    @38
    @37
    cN
    cn0
    wcel
    #
    @36
    @37
    @39
    wb
    @29
    cN
    @29
    cN
    cn0
    eleq1
    eqcoms
    @39
    @36
    cN
    elnn0uz
    biimpi
    syl6bi
    ax-mp
    3syl
    #
    cc0
    cN
    fzosplitsn
    syl
    eqtrd
    wph
    @2
    cI
    @19
    cun
    #
    cdm
    @21
    wph
    @1
    @41
    wlkp1.u
    dmeqd
    cI
    @19
    dmun
    syl6eq
    feq123d
    mpbird
    @2
    cH
    iswrdb
    sylibr
    wph
    @7
    cc0
    @33
    cfz
    co
    #
    cV
    cP
    @33
    cC
    cop
    csn
    #
    cun
    #
    wf
    #
    wph
    @45
    cc0
    cN
    cfz
    co
    #
    @33
    csn
    #
    cun
    #
    cV
    cV
    cun
    #
    @44
    wf
    #
    wph
    @46
    cV
    cP
    wf
    #
    @47
    cV
    @43
    wf
    @46
    @47
    cin
    c0
    wceq
    #
    @50
    wph
    cc0
    @29
    cfz
    co
    #
    cV
    cP
    wf
    #
    @51
    wph
    @27
    @54
    wlkp1.w
    cP
    cF
    cG
    cV
    wlkp1.v
    wlkp
    syl
    @46
    @53
    cV
    cP
    cN
    @29
    cc0
    cfz
    wlkp1.n
    oveq2i
    feq2i
    sylibr
    wph
    @33
    cC
    cvv
    cV
    wph
    cN
    c1
    caddc
    ovexd
    wlkp1.c
    fsnd
    @52
    wph
    cc0
    cN
    fzp1disj
    a1i
    @46
    @47
    cV
    cV
    cP
    @43
    fun
    syl21anc
    wph
    @42
    cV
    @48
    @49
    @44
    wph
    @36
    @42
    @48
    wceq
    @40
    cc0
    cN
    fzsuc
    syl
    cV
    @49
    wceq
    wph
    @49
    cV
    cV
    unidm
    eqcomi
    a1i
    feq23d
    mpbird
    wph
    @5
    @42
    @6
    cV
    cQ
    @44
    cQ
    @44
    wceq
    wph
    wlkp1.q
    a1i
    wph
    @4
    @33
    cc0
    cfz
    @35
    oveq2d
    wlkp1.s
    feq123d
    mpbird
    wph
    cB
    cC
    cP
    cQ
    cS
    vk
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1.q
    wlkp1.s
    wlkp1.l
    wlkp1lem8
    wph
    cS
    cvv
    wcel
    cH
    cvv
    wcel
    cQ
    cvv
    wcel
    w3a
    @0
    @3
    @7
    @13
    w3a
    wb
    wph
    cB
    cC
    cP
    cQ
    cS
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1.q
    wlkp1.s
    wlkp1lem4
    cQ
    cvv
    vk
    cH
    cS
    @1
    @6
    cvv
    cvv
    @6
    eqid
    @1
    eqid
    iswlk
    syl
    mpbir3and
end
