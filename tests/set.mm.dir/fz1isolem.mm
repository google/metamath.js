include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cres.mm"
include "ccom.mm"
include "cvv.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "clt.mm"
include "wiso.mm"
include "cv.mm"
include "wex.mm"
include "wf.mm"
include "wf1o.mm"
include "cdm.mm"
include "cep.mm"
include "cn0.mm"
include "hashcl.mm"
include "adantl.mm"
include "cn.mm"
include "com.mm"
include "caddc.mm"
include "cuz.mm"
include "wceq.mm"
include "nnuz.mm"
include "1z.mm"
include "om2uzisoi.mm"
include "isoeq5.mm"
include "mpbiri.mm"
include "ax-mp.mm"
include "isocnv.mm"
include "nn0p1nn.mm"
include "cin.mm"
include "csn.mm"
include "cima.mm"
include "fvex.mm"
include "epini.mm"
include "ineq2i.mm"
include "eqtr4i.mm"
include "isoini2.mm"
include "sylancr.mm"
include "syl.mm"
include "wb.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "nnz.mm"
include "nn0zd.mm"
include "eluz.mm"
include "syl2anr.mm"
include "zleltp1.mm"
include "ovex.mm"
include "vex.mm"
include "eliniseg.mm"
include "syl6bbr.mm"
include "bitr2d.mm"
include "pm5.32da.mm"
include "elin2.mm"
include "elfzuzb.mm"
include "elnnuz.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "isoeq4.mm"
include "mpbid.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "con0.mm"
include "oion.mm"
include "cen.mm"
include "simpr.mm"
include "wwe.mm"
include "wofi.mm"
include "oien.mm"
include "syl2anc.mm"
include "enfii.mm"
include "elind.mm"
include "onfin2.mm"
include "syl6eleqr.mm"
include "cmin.mm"
include "eqid.mm"
include "0z.mm"
include "uzrdgxfr.mm"
include "1m0e1.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "ccrd.mm"
include "ensymd.mm"
include "cardennn.mm"
include "fveq2d.mm"
include "hashgval.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "isof1o.mm"
include "f1ocnvfv1.mm"
include "ineq2d.mm"
include "wss.mm"
include "word.mm"
include "ordom.mm"
include "ordelss.mm"
include "sseqin2.mm"
include "sylib.mm"
include "syl5eq.mm"
include "oiiso.mm"
include "isotr.mm"
include "f1of.mm"
include "3syl.mm"
include "fzfid.mm"
include "fex.mm"
include "isoeq1.mm"
include "spcegv.mm"
include "sylc.mm"

theorem fz1isolem
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  let cO: class O
  assume fz1iso.1: |- G = ( rec ( ( n e. _V |-> ( n + 1 ) ) , 1 ) |` _om )
  assume fz1iso.2: |- B = ( NN i^i ( `' < " { ( ( # ` A ) + 1 ) } ) )
  assume fz1iso.3: |- C = ( _om i^i ( `' G ` ( ( # ` A ) + 1 ) ) )
  assume fz1iso.4: |- O = OrdIso ( R , A )

  disjoint f n
  disjoint A f
  disjoint A n
  disjoint B f
  disjoint G f
  disjoint O f
  disjoint R f
  assert |- ( ( R Or A /\ A e. Fin ) -> E. f f Isom < , R ( ( 1 ... ( # ` A ) ) , A ) )

  proof
    cA
    cR
    wor
    #
    cA
    cfn
    wcel
    #
    wa
    #
    cO
    cG
    ccnv
    #
    cB
    cres
    #
    ccom
    #
    cvv
    wcel
    #
    c1
    cA
    chash
    cfv
    #
    cfz
    co
    #
    cA
    clt
    cR
    @5
    wiso
    #
    @8
    cA
    clt
    cR
    vf
    cv
    #
    wiso
    #
    vf
    wex
    @2
    @8
    cA
    @5
    wf
    #
    @8
    cfn
    wcel
    @6
    @2
    @9
    @8
    cA
    @5
    wf1o
    @12
    @2
    @8
    cO
    cdm
    #
    clt
    cep
    @4
    wiso
    #
    @13
    cA
    cep
    cR
    cO
    wiso
    #
    @9
    @2
    @8
    cC
    clt
    cep
    @4
    wiso
    #
    @14
    @2
    cB
    cC
    clt
    cep
    @4
    wiso
    #
    @16
    @2
    @7
    cn0
    wcel
    #
    @17
    @1
    @18
    @0
    cA
    hashcl
    adantl
    #
    @18
    cn
    com
    clt
    cep
    @3
    wiso
    #
    @7
    c1
    caddc
    co
    #
    cn
    wcel
    @17
    com
    cn
    cep
    clt
    cG
    wiso
    #
    @20
    cn
    c1
    cuz
    cfv
    #
    wceq
    #
    @22
    nnuz
    @24
    @22
    com
    @23
    cep
    clt
    cG
    wiso
    vn
    c1
    cG
    1z
    fz1iso.1
    om2uzisoi
    com
    cn
    @23
    cep
    clt
    cG
    isoeq5
    mpbiri
    ax-mp
    #
    com
    cn
    cep
    clt
    cG
    isocnv
    ax-mp
    @7
    nn0p1nn
    cn
    com
    cB
    cC
    clt
    cep
    @3
    @21
    fz1iso.2
    cC
    com
    @21
    @3
    cfv
    #
    cin
    #
    com
    cep
    ccnv
    @26
    csn
    cima
    #
    cin
    fz1iso.3
    @28
    @26
    com
    @26
    @21
    @3
    fvex
    epini
    ineq2i
    eqtr4i
    isoini2
    sylancr
    syl
    @2
    cB
    @8
    wceq
    @17
    @16
    wb
    @2
    vf
    cB
    @8
    @2
    @10
    cn
    wcel
    #
    @10
    clt
    ccnv
    @21
    csn
    cima
    #
    wcel
    #
    wa
    @29
    @7
    @10
    cuz
    cfv
    wcel
    #
    wa
    #
    @10
    cB
    wcel
    @10
    @8
    wcel
    #
    @2
    @29
    @31
    @32
    @2
    @29
    wa
    #
    @32
    @10
    @7
    cle
    wbr
    #
    @31
    @29
    @10
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @32
    @36
    wb
    @2
    @10
    nnz
    #
    @2
    @7
    @19
    nn0zd
    #
    @10
    @7
    eluz
    syl2anr
    @35
    @36
    @10
    @21
    clt
    wbr
    #
    @31
    @29
    @37
    @38
    @36
    @41
    wb
    @2
    @39
    @40
    @10
    @7
    zleltp1
    syl2anr
    @21
    cvv
    wcel
    @31
    @41
    wb
    @7
    c1
    caddc
    ovex
    clt
    @21
    @10
    cvv
    vf
    vex
    eliniseg
    ax-mp
    syl6bbr
    bitr2d
    pm5.32da
    @10
    cn
    @30
    cB
    fz1iso.2
    elin2
    @34
    @10
    @23
    wcel
    #
    @32
    wa
    @33
    @10
    c1
    @7
    elfzuzb
    @29
    @42
    @32
    @10
    elnnuz
    anbi1i
    bitr4i
    3bitr4g
    eqrdv
    cB
    cC
    @8
    clt
    cep
    @4
    isoeq4
    syl
    mpbid
    @2
    cC
    @13
    wceq
    @16
    @14
    wb
    @2
    cC
    @27
    @13
    fz1iso.3
    @2
    @27
    com
    @13
    cin
    #
    @13
    @2
    @26
    @13
    com
    @2
    @13
    cG
    cfv
    #
    @3
    cfv
    #
    @26
    @13
    @2
    @44
    @21
    @3
    @2
    @44
    @13
    vn
    cvv
    vn
    cv
    c1
    caddc
    co
    cmpt
    cc0
    crdg
    com
    cres
    #
    cfv
    #
    c1
    caddc
    co
    #
    @21
    @2
    @13
    com
    wcel
    #
    @44
    @48
    wceq
    @2
    @13
    con0
    cfn
    cin
    com
    @2
    con0
    cfn
    @13
    @1
    @13
    con0
    wcel
    @0
    cA
    cR
    cO
    cfn
    fz1iso.4
    oion
    adantl
    @2
    @1
    @13
    cA
    cen
    wbr
    #
    @13
    cfn
    wcel
    @0
    @1
    simpr
    #
    @2
    @1
    cA
    cR
    wwe
    #
    @50
    @51
    cA
    cR
    wofi
    #
    cA
    cR
    cO
    cfn
    fz1iso.4
    oien
    syl2anc
    #
    @13
    cA
    enfii
    syl2anc
    elind
    onfin2
    syl6eleqr
    #
    @49
    @44
    @47
    c1
    cc0
    cmin
    co
    #
    caddc
    co
    @48
    vn
    c1
    cc0
    cG
    @46
    @13
    fz1iso.1
    @46
    eqid
    #
    1z
    0z
    uzrdgxfr
    @56
    c1
    @47
    caddc
    1m0e1
    oveq2i
    syl6eq
    syl
    @2
    @47
    @7
    c1
    caddc
    @2
    cA
    ccrd
    cfv
    #
    @46
    cfv
    #
    @47
    @7
    @2
    @58
    @13
    @46
    @2
    cA
    @13
    cen
    wbr
    @49
    @58
    @13
    wceq
    @2
    @13
    cA
    @54
    ensymd
    @55
    cA
    @13
    cardennn
    syl2anc
    fveq2d
    @1
    @59
    @7
    wceq
    @0
    vn
    cA
    @46
    @57
    hashgval
    adantl
    eqtr3d
    oveq1d
    eqtrd
    fveq2d
    @2
    com
    cn
    cG
    wf1o
    #
    @49
    @45
    @13
    wceq
    @22
    @60
    @25
    com
    cn
    cep
    clt
    cG
    isof1o
    ax-mp
    @55
    com
    cn
    @13
    cG
    f1ocnvfv1
    sylancr
    eqtr3d
    ineq2d
    @2
    @13
    com
    wss
    #
    @43
    @13
    wceq
    @2
    com
    word
    @49
    @61
    ordom
    @55
    com
    @13
    ordelss
    sylancr
    @13
    com
    sseqin2
    sylib
    eqtrd
    syl5eq
    @8
    cC
    @13
    clt
    cep
    @4
    isoeq5
    syl
    mpbid
    @2
    @1
    @52
    @15
    @51
    @53
    cA
    cR
    cO
    cfn
    fz1iso.4
    oiiso
    syl2anc
    @8
    @13
    cA
    clt
    cep
    cR
    cO
    @4
    isotr
    syl2anc
    #
    @8
    cA
    clt
    cR
    @5
    isof1o
    @8
    cA
    @5
    f1of
    3syl
    @2
    c1
    @7
    fzfid
    @8
    cA
    cfn
    @5
    fex
    syl2anc
    @62
    @11
    @9
    vf
    @5
    cvv
    @8
    cA
    clt
    cR
    @5
    @10
    isoeq1
    spcegv
    sylc
end
