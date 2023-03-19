include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "csb.mm"
include "cn0.mm"
include "wcel.mm"
include "wsbc.mm"
include "csbif.mm"
include "wb.mm"
include "eqsbc3.mm"
include "syl.mm"
include "sbcbr2g.mm"
include "csbvarg.mm"
include "breq2d.mm"
include "bitrd.mm"
include "ifbid.mm"
include "syl5eq.mm"
include "ifbieq2d.mm"
include "wa.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "wn.mm"
include "eqcomd.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "wi.mm"
include "ex.mm"
include "imp.mm"
include "ad3antrrr.mm"
include "simplll.mm"
include "ancom.mm"
include "anbi2i.mm"
include "anass.mm"
include "bicomi.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "3bitr4i.mm"
include "an32.mm"
include "bitri.mm"
include "wne.mm"
include "df-ne.mm"
include "cn.mm"
include "elnnne0.mm"
include "nngt0.mm"
include "sylbir.mm"
include "expcom.mm"
include "mpan9.mm"
include "cle.mm"
include "nn0red.mm"
include "nnred.mm"
include "lenltd.mm"
include "biimprd.mm"
include "adantld.mm"
include "nesym.mm"
include "biimpri.mm"
include "ad2antll.mm"
include "cr.mm"
include "ltlend.mm"
include "mpbir2and.mm"
include "w3a.mm"
include "syl3anc.mm"
include "ifclda.mm"
include "fvmpts.mm"
include "syl2anc.mm"
include "ifeqda.mm"
include "3eqtrd.mm"

theorem fvmptnn04if
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cV: class V
  let cY: class Y
  assume fvmptnn04if.g: |- G = ( n e. NN0 |-> if ( n = 0 , A , if ( n = S , C , if ( S < n , D , B ) ) ) )
  assume fvmptnn04if.s: |- ( ph -> S e. NN )
  assume fvmptnn04if.n: |- ( ph -> N e. NN0 )
  assume fvmptnn04if.y: |- ( ph -> Y e. V )
  assume fvmptnn04if.a: |- ( ( ph /\ N = 0 ) -> Y = [_ N / n ]_ A )
  assume fvmptnn04if.b: |- ( ( ph /\ 0 < N /\ N < S ) -> Y = [_ N / n ]_ B )
  assume fvmptnn04if.c: |- ( ( ph /\ N = S ) -> Y = [_ N / n ]_ C )
  assume fvmptnn04if.d: |- ( ( ph /\ S < N ) -> Y = [_ N / n ]_ D )

  disjoint N n
  disjoint S n
  assert |- ( ph -> ( G ` N ) = Y )

  proof
    wph
    cN
    cG
    cfv
    #
    vn
    cN
    vn
    cv
    #
    cc0
    wceq
    #
    cA
    @1
    cS
    wceq
    #
    cC
    cS
    @1
    clt
    wbr
    #
    cD
    cB
    cif
    #
    cif
    #
    cif
    #
    csb
    #
    cN
    cc0
    wceq
    #
    vn
    cN
    cA
    csb
    #
    cN
    cS
    wceq
    #
    vn
    cN
    cC
    csb
    #
    cS
    cN
    clt
    wbr
    #
    vn
    cN
    cD
    csb
    #
    vn
    cN
    cB
    csb
    #
    cif
    #
    cif
    #
    cif
    #
    cY
    wph
    cN
    cn0
    wcel
    #
    @8
    cV
    wcel
    @0
    @8
    wceq
    fvmptnn04if.n
    wph
    @8
    @18
    cV
    wph
    @8
    @2
    vn
    cN
    wsbc
    #
    @10
    vn
    cN
    @6
    csb
    #
    cif
    @18
    @2
    vn
    cN
    cA
    @6
    csbif
    wph
    @20
    @9
    @21
    @17
    @10
    wph
    @19
    @20
    @9
    wb
    fvmptnn04if.n
    vn
    cN
    cc0
    cn0
    eqsbc3
    syl
    wph
    @21
    @3
    vn
    cN
    wsbc
    #
    @12
    vn
    cN
    @5
    csb
    #
    cif
    @17
    @3
    vn
    cN
    cC
    @5
    csbif
    wph
    @22
    @11
    @23
    @16
    @12
    wph
    @19
    @22
    @11
    wb
    fvmptnn04if.n
    vn
    cN
    cS
    cn0
    eqsbc3
    syl
    wph
    @23
    @4
    vn
    cN
    wsbc
    #
    @14
    @15
    cif
    @16
    @4
    vn
    cN
    cD
    cB
    csbif
    wph
    @24
    @13
    @14
    @15
    wph
    @24
    cS
    vn
    cN
    @1
    csb
    #
    clt
    wbr
    #
    @13
    wph
    @19
    @24
    @26
    wb
    fvmptnn04if.n
    vn
    cN
    cS
    @1
    clt
    cn0
    sbcbr2g
    syl
    wph
    @25
    cN
    cS
    clt
    wph
    @19
    @25
    cN
    wceq
    fvmptnn04if.n
    vn
    cN
    cn0
    csbvarg
    syl
    breq2d
    bitrd
    ifbid
    syl5eq
    ifbieq2d
    syl5eq
    ifbieq2d
    syl5eq
    #
    wph
    @9
    @10
    @17
    cV
    wph
    @9
    wa
    #
    cY
    @10
    cV
    fvmptnn04if.a
    wph
    cY
    cV
    wcel
    #
    @9
    fvmptnn04if.y
    adantr
    eqeltrrd
    wph
    @9
    wn
    #
    wa
    #
    @11
    @12
    @16
    cV
    @31
    @11
    wa
    @12
    cY
    cV
    wph
    @11
    @12
    cY
    wceq
    @30
    wph
    @11
    wa
    cY
    @12
    fvmptnn04if.c
    eqcomd
    adantlr
    #
    wph
    @29
    @30
    @11
    fvmptnn04if.y
    ad2antrr
    eqeltrd
    @31
    @11
    wn
    #
    wa
    #
    @13
    @14
    @15
    cV
    @34
    @13
    wa
    @14
    cY
    cV
    @34
    @13
    @14
    cY
    wceq
    #
    wph
    @13
    @35
    wi
    @30
    @33
    wph
    @13
    @35
    wph
    @13
    wa
    cY
    @14
    fvmptnn04if.d
    eqcomd
    ex
    ad2antrr
    imp
    #
    wph
    @29
    @30
    @33
    @13
    fvmptnn04if.y
    ad3antrrr
    eqeltrd
    @34
    @13
    wn
    #
    wa
    #
    @15
    cY
    cV
    @38
    wph
    cc0
    cN
    clt
    wbr
    #
    cN
    cS
    clt
    wbr
    #
    @15
    cY
    wceq
    wph
    @30
    @33
    @37
    simplll
    @38
    wph
    @30
    @33
    @37
    wa
    #
    wa
    #
    wa
    #
    @39
    @43
    @30
    @33
    wa
    #
    wph
    wa
    #
    @37
    wa
    #
    @38
    @44
    @37
    wph
    wa
    #
    wa
    #
    @44
    wph
    @37
    wa
    #
    wa
    @43
    @46
    @47
    @49
    @44
    @37
    wph
    ancom
    anbi2i
    @43
    @42
    wph
    wa
    @44
    @37
    wa
    #
    wph
    wa
    @48
    wph
    @42
    ancom
    @42
    @50
    wph
    @50
    @42
    @30
    @33
    @37
    anass
    bicomi
    anbi1i
    @44
    @37
    wph
    anass
    3bitri
    @44
    wph
    @37
    anass
    3bitr4i
    @45
    @34
    @37
    @45
    @30
    wph
    wa
    #
    @33
    wa
    @34
    @30
    @33
    wph
    an32
    @51
    @31
    @33
    @30
    wph
    ancom
    anbi1i
    bitri
    anbi1i
    bitri
    #
    wph
    @19
    @42
    @39
    fvmptnn04if.n
    @30
    @19
    @39
    wi
    #
    @41
    @30
    cN
    cc0
    wne
    #
    @53
    cN
    cc0
    df-ne
    @19
    @54
    @39
    @19
    @54
    wa
    cN
    cn
    wcel
    @39
    cN
    elnnne0
    cN
    nngt0
    sylbir
    expcom
    sylbir
    adantr
    mpan9
    sylbir
    @38
    @43
    @40
    @52
    @43
    @40
    cN
    cS
    cle
    wbr
    #
    cS
    cN
    wne
    #
    wph
    @42
    @55
    wph
    @41
    @55
    @30
    wph
    @37
    @55
    @33
    wph
    @55
    @37
    wph
    cN
    cS
    wph
    cN
    fvmptnn04if.n
    nn0red
    #
    wph
    cS
    fvmptnn04if.s
    nnred
    #
    lenltd
    biimprd
    adantld
    adantld
    imp
    @41
    @56
    wph
    @30
    @33
    @56
    @37
    @56
    @33
    cS
    cN
    nesym
    biimpri
    adantr
    ad2antll
    @43
    cN
    cS
    wph
    cN
    cr
    wcel
    @42
    @57
    adantr
    wph
    cS
    cr
    wcel
    @42
    @58
    adantr
    ltlend
    mpbir2and
    sylbir
    wph
    @39
    @40
    w3a
    cY
    @15
    fvmptnn04if.b
    eqcomd
    syl3anc
    #
    wph
    @29
    @30
    @33
    @37
    fvmptnn04if.y
    ad3antrrr
    eqeltrd
    ifclda
    ifclda
    ifclda
    eqeltrd
    vn
    cN
    @7
    cn0
    cG
    cV
    fvmptnn04if.g
    fvmpts
    syl2anc
    @27
    wph
    @9
    @10
    @17
    cY
    @28
    cY
    @10
    fvmptnn04if.a
    eqcomd
    @31
    @11
    @12
    @16
    cY
    @32
    @34
    @13
    @14
    @15
    cY
    @36
    @59
    ifeqda
    ifeqda
    ifeqda
    3eqtrd
end
