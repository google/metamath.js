include "cidom.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cfv.mm"
include "wss.mm"
include "csubg.mm"
include "cbs.mm"
include "cgrp.mm"
include "cacs.mm"
include "cmre.mm"
include "cdomn.mm"
include "crg.mm"
include "simpll.mm"
include "ccrg.mm"
include "isidom.mm"
include "simprbi.mm"
include "domnring.mm"
include "cui.mm"
include "eqid.mm"
include "unitgrp.mm"
include "4syl.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "wceq.mm"
include "simprl.mm"
include "cn0.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "odf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mp2b.mm"
include "sylib.mm"
include "simpld.mm"
include "snssd.mm"
include "mrcssidd.mm"
include "snssg.mm"
include "syl.mm"
include "mpbird.mm"
include "cv.mm"
include "chash.mm"
include "wrmo.mm"
include "idomsubgmo.mm"
include "adantr.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "simprd.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "odhash2.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "simprr.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rmoi.mm"
include "syl122anc.mm"
include "eleqtrd.mm"

theorem proot1mul
  let cR: class R
  let cG: class G
  let cK: class K
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume idomsubgmo.g: |- G = ( ( mulGrp ` R ) |`s ( Unit ` R ) )
  assume proot1mul.o: |- O = ( od ` G )
  assume proot1mul.k: |- K = ( mrCls ` ( SubGrp ` G ) )


  assert |- ( ( ( R e. IDomn /\ N e. NN ) /\ ( X e. ( `' O " { N } ) /\ Y e. ( `' O " { N } ) ) ) -> X e. ( K ` { Y } ) )

  proof
    cR
    cidom
    wcel
    #
    cN
    cn
    wcel
    #
    wa
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
    cY
    @3
    wcel
    #
    wa
    #
    wa
    #
    cX
    cX
    csn
    #
    cK
    cfv
    #
    cY
    csn
    #
    cK
    cfv
    #
    @7
    cX
    @9
    wcel
    #
    @8
    @9
    wss
    #
    @7
    cG
    csubg
    cfv
    #
    @8
    cK
    cG
    cbs
    cfv
    #
    @7
    cG
    cgrp
    wcel
    #
    @14
    @15
    cacs
    cfv
    wcel
    @14
    @15
    cmre
    cfv
    wcel
    #
    @7
    @0
    cR
    cdomn
    wcel
    #
    cR
    crg
    wcel
    @16
    @0
    @1
    @6
    simpll
    @0
    cR
    ccrg
    wcel
    @18
    cR
    isidom
    simprbi
    cR
    domnring
    cR
    cR
    cui
    cfv
    #
    cG
    @19
    eqid
    idomsubgmo.g
    unitgrp
    4syl
    #
    @15
    cG
    @15
    eqid
    #
    subgacs
    @14
    @15
    acsmre
    3syl
    #
    proot1mul.k
    @7
    cX
    @15
    @7
    cX
    @15
    wcel
    #
    cX
    cO
    cfv
    #
    cN
    wceq
    #
    @7
    @4
    @23
    @25
    wa
    #
    @2
    @4
    @5
    simprl
    #
    @15
    cn0
    cO
    wf
    #
    cO
    @15
    wfn
    #
    @4
    @26
    wb
    cG
    cO
    @15
    @21
    proot1mul.o
    odf
    #
    @15
    cn0
    cO
    ffn
    #
    @15
    cN
    cX
    cO
    fniniseg
    mp2b
    sylib
    #
    simpld
    #
    snssd
    #
    mrcssidd
    @7
    @4
    @12
    @13
    wb
    @27
    cX
    @9
    @3
    snssg
    syl
    mpbird
    @7
    vx
    cv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    vx
    @14
    wrmo
    #
    @9
    @14
    wcel
    #
    @9
    chash
    cfv
    #
    cN
    wceq
    #
    @11
    @14
    wcel
    #
    @11
    chash
    cfv
    #
    cN
    wceq
    #
    @9
    @11
    wceq
    @2
    @38
    @6
    vx
    cR
    cG
    cN
    idomsubgmo.g
    idomsubgmo
    adantr
    @7
    @17
    @8
    @15
    wss
    @39
    @22
    @34
    @14
    @8
    cK
    @15
    proot1mul.k
    mrccl
    syl2anc
    @7
    @40
    @24
    cN
    @7
    @16
    @23
    @24
    cn
    wcel
    @40
    @24
    wceq
    @20
    @33
    @7
    @24
    cN
    cn
    @7
    @23
    @25
    @32
    simprd
    #
    @0
    @1
    @6
    simplr
    #
    eqeltrd
    cX
    cG
    cK
    cO
    @15
    @21
    proot1mul.o
    proot1mul.k
    odhash2
    syl3anc
    @45
    eqtrd
    @7
    @17
    @10
    @15
    wss
    @42
    @22
    @7
    cY
    @15
    @7
    cY
    @15
    wcel
    #
    cY
    cO
    cfv
    #
    cN
    wceq
    #
    @7
    @5
    @47
    @49
    wa
    #
    @2
    @4
    @5
    simprr
    @28
    @29
    @5
    @50
    wb
    @30
    @31
    @15
    cN
    cY
    cO
    fniniseg
    mp2b
    sylib
    #
    simpld
    #
    snssd
    @14
    @10
    cK
    @15
    proot1mul.k
    mrccl
    syl2anc
    @7
    @43
    @48
    cN
    @7
    @16
    @47
    @48
    cn
    wcel
    @43
    @48
    wceq
    @20
    @52
    @7
    @48
    cN
    cn
    @7
    @47
    @49
    @51
    simprd
    #
    @46
    eqeltrd
    cY
    cG
    cK
    cO
    @15
    @21
    proot1mul.o
    proot1mul.k
    odhash2
    syl3anc
    @53
    eqtrd
    @37
    @41
    @44
    vx
    @14
    @9
    @11
    @35
    @9
    wceq
    @36
    @40
    cN
    @35
    @9
    chash
    fveq2
    eqeq1d
    @35
    @11
    wceq
    @36
    @43
    cN
    @35
    @11
    chash
    fveq2
    eqeq1d
    rmoi
    syl122anc
    eleqtrd
end
