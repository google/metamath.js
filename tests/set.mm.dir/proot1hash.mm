include "cidom.mm"
include "wcel.mm"
include "cn.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "csubg.mm"
include "cmrc.mm"
include "crab.mm"
include "cphi.mm"
include "cbs.mm"
include "cn0.mm"
include "wf.mm"
include "wfn.mm"
include "eqid.mm"
include "odf.mm"
include "ffn.mm"
include "fniniseg2.mm"
include "mp2b.mm"
include "cin.mm"
include "wa.mm"
include "simp3.mm"
include "wb.mm"
include "fniniseg.mm"
include "sylib.mm"
include "simprd.mm"
include "eqeq2d.mm"
include "rabbidv.mm"
include "cmre.mm"
include "wss.mm"
include "cgrp.mm"
include "cacs.mm"
include "cdomn.mm"
include "crg.mm"
include "ccrg.mm"
include "isidom.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "domnring.mm"
include "cui.mm"
include "unitgrp.mm"
include "3syl.mm"
include "subgacs.mm"
include "acsmre.mm"
include "mrcssv.mm"
include "dfrab3ss.mm"
include "incom.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "simpl3.mm"
include "proot1mul.mm"
include "syl22anc.mm"
include "ex.mm"
include "ssrdv.mm"
include "syl5eqssr.mm"
include "df-ss.mm"
include "syl5eq.mm"
include "3eqtrrd.mm"
include "fveq2d.mm"
include "simpld.mm"
include "simp2.mm"
include "eqeltrd.mm"
include "odngen.mm"
include "syl3anc.mm"
include "3eqtrd.mm"

theorem proot1hash
  let cR: class R
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let vx: setvar x
  assume proot1hash.g: |- G = ( ( mulGrp ` R ) |`s ( Unit ` R ) )
  assume proot1hash.o: |- O = ( od ` G )


  assert |- ( ( R e. IDomn /\ N e. NN /\ X e. ( `' O " { N } ) ) -> ( # ` ( `' O " { N } ) ) = ( phi ` N ) )

  proof
    cR
    cidom
    wcel
    #
    cN
    cn
    wcel
    #
    cX
    cO
    ccnv
    cN
    csn
    cima
    #
    wcel
    #
    w3a
    #
    @2
    chash
    cfv
    vx
    cv
    #
    cO
    cfv
    #
    cX
    cO
    cfv
    #
    wceq
    #
    vx
    cX
    csn
    #
    cG
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cfv
    #
    crab
    #
    chash
    cfv
    #
    @7
    cphi
    cfv
    #
    cN
    cphi
    cfv
    @4
    @2
    @13
    chash
    @4
    @2
    @6
    cN
    wceq
    #
    vx
    cG
    cbs
    cfv
    #
    crab
    #
    @13
    @17
    cn0
    cO
    wf
    #
    cO
    @17
    wfn
    #
    @2
    @18
    wceq
    cG
    cO
    @17
    @17
    eqid
    #
    proot1hash.o
    odf
    #
    @17
    cn0
    cO
    ffn
    #
    vx
    @17
    cN
    cO
    fniniseg2
    mp2b
    #
    @4
    @13
    @16
    vx
    @12
    crab
    #
    @12
    @18
    cin
    #
    @18
    @4
    @8
    @16
    vx
    @12
    @4
    @7
    cN
    @6
    @4
    cX
    @17
    wcel
    #
    @7
    cN
    wceq
    #
    @4
    @3
    @27
    @28
    wa
    #
    @0
    @1
    @3
    simp3
    @19
    @20
    @3
    @29
    wb
    @22
    @23
    @17
    cN
    cX
    cO
    fniniseg
    mp2b
    sylib
    #
    simprd
    #
    eqeq2d
    rabbidv
    @4
    @10
    @17
    cmre
    cfv
    wcel
    #
    @12
    @17
    wss
    @25
    @26
    wceq
    @4
    cG
    cgrp
    wcel
    #
    @10
    @17
    cacs
    cfv
    wcel
    @32
    @4
    cR
    cdomn
    wcel
    #
    cR
    crg
    wcel
    @33
    @0
    @1
    @34
    @3
    @0
    cR
    ccrg
    wcel
    @34
    cR
    isidom
    simprbi
    3ad2ant1
    cR
    domnring
    cR
    cR
    cui
    cfv
    #
    cG
    @35
    eqid
    proot1hash.g
    unitgrp
    3syl
    #
    @17
    cG
    @21
    subgacs
    @10
    @17
    acsmre
    3syl
    @10
    @9
    @11
    @17
    @11
    eqid
    #
    mrcssv
    @16
    vx
    @12
    @17
    dfrab3ss
    3syl
    @4
    @26
    @18
    @12
    cin
    #
    @18
    @12
    @18
    incom
    @4
    @18
    @12
    wss
    @38
    @18
    wceq
    @4
    @18
    @2
    @12
    @24
    @4
    vx
    @2
    @12
    @4
    @5
    @2
    wcel
    #
    @5
    @12
    wcel
    #
    @4
    @39
    wa
    @0
    @1
    @39
    @3
    @40
    @0
    @1
    @3
    @39
    simpl1
    @0
    @1
    @3
    @39
    simpl2
    @4
    @39
    simpr
    @0
    @1
    @3
    @39
    simpl3
    cR
    cG
    @11
    cN
    cO
    @5
    cX
    proot1hash.g
    proot1hash.o
    @37
    proot1mul
    syl22anc
    ex
    ssrdv
    syl5eqssr
    @18
    @12
    df-ss
    sylib
    syl5eq
    3eqtrrd
    syl5eq
    fveq2d
    @4
    @33
    @27
    @7
    cn
    wcel
    @14
    @15
    wceq
    @36
    @4
    @27
    @28
    @30
    simpld
    @4
    @7
    cN
    cn
    @31
    @0
    @1
    @3
    simp2
    eqeltrd
    vx
    cX
    cG
    @11
    cO
    @17
    @21
    proot1hash.o
    @37
    odngen
    syl3anc
    @4
    @7
    cN
    cphi
    @31
    fveq2d
    3eqtrd
end
