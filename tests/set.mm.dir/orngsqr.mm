include "corng.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "orngmul.mm"
include "syl122anc.mm"
include "wn.mm"
include "cminusg.mm"
include "cfv.mm"
include "cgrp.mm"
include "crg.mm"
include "orngring.mm"
include "ad2antrr.mm"
include "ringgrp.mm"
include "syl.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "cplusg.mm"
include "comnd.mm"
include "cogrp.mm"
include "orngogrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "grpidcl.mm"
include "cplt.mm"
include "wceq.mm"
include "wo.mm"
include "w3a.mm"
include "simpl.mm"
include "3syl.mm"
include "3jca.mm"
include "pltle.mm"
include "con3dimp.mm"
include "sylan.mm"
include "w3o.mm"
include "wor.mm"
include "ctos.mm"
include "omndtos.mm"
include "cid.mm"
include "cres.mm"
include "wss.mm"
include "tosso.mm"
include "ibi.mm"
include "simpld.mm"
include "solin.mm"
include "syl12anc.mm"
include "3orass.mm"
include "sylib.mm"
include "orel1.mm"
include "sylc.mm"
include "orcom.mm"
include "eqcom.mm"
include "orbi2i.mm"
include "bitri.mm"
include "cpo.mm"
include "wb.mm"
include "tospos.mm"
include "pleval2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "omndadd.mm"
include "syl131anc.mm"
include "grprinv.mm"
include "grplid.mm"
include "3brtr3d.mm"
include "ringm2neg.mm"
include "breqtrd.mm"
include "pm2.61dan.mm"

theorem orngsqr
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let cY: class Y
  assume orngmul.0: |- B = ( Base ` R )
  assume orngmul.1: |- .<_ = ( le ` R )
  assume orngmul.2: |- .0. = ( 0g ` R )
  assume orngmul.3: |- .x. = ( .r ` R )


  assert |- ( ( R e. oRing /\ X e. B ) -> .0. .<_ ( X .x. X ) )

  proof
    cR
    corng
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    c.0
    cX
    c.le
    wbr
    #
    c.0
    cX
    cX
    c.x
    co
    #
    c.le
    wbr
    #
    @2
    @3
    wa
    @0
    @1
    @3
    @1
    @3
    @5
    @0
    @1
    @3
    simpll
    @0
    @1
    @3
    simplr
    #
    @2
    @3
    simpr
    #
    @6
    @7
    cB
    cR
    c.x
    c.le
    cX
    cX
    c.0
    orngmul.0
    orngmul.1
    orngmul.2
    orngmul.3
    orngmul
    syl122anc
    @2
    @3
    wn
    #
    wa
    #
    c.0
    cX
    cR
    cminusg
    cfv
    #
    cfv
    #
    @11
    c.x
    co
    #
    @4
    c.le
    @9
    @0
    @11
    cB
    wcel
    #
    c.0
    @11
    c.le
    wbr
    #
    @13
    @14
    c.0
    @12
    c.le
    wbr
    @0
    @1
    @8
    simpll
    #
    @9
    cR
    cgrp
    wcel
    #
    @1
    @13
    @9
    cR
    crg
    wcel
    #
    @16
    @0
    @17
    @1
    @8
    cR
    orngring
    #
    ad2antrr
    #
    cR
    ringgrp
    #
    syl
    #
    @0
    @1
    @8
    simplr
    #
    cB
    cR
    @10
    cX
    orngmul.0
    @10
    eqid
    #
    grpinvcl
    syl2anc
    #
    @9
    cX
    @11
    cR
    cplusg
    cfv
    #
    co
    #
    c.0
    @11
    @25
    co
    #
    c.0
    @11
    c.le
    @9
    cR
    comnd
    wcel
    #
    @1
    c.0
    cB
    wcel
    #
    @13
    cX
    c.0
    c.le
    wbr
    #
    @26
    @27
    c.le
    wbr
    @9
    @0
    @28
    @15
    @0
    cR
    cogrp
    wcel
    #
    @28
    cR
    orngogrp
    @31
    @16
    @28
    cR
    isogrp
    simprbi
    syl
    #
    syl
    @22
    @9
    @16
    @29
    @21
    cB
    cR
    c.0
    orngmul.0
    orngmul.2
    grpidcl
    #
    syl
    #
    @24
    @9
    @30
    cX
    c.0
    cR
    cplt
    cfv
    #
    wbr
    #
    cX
    c.0
    wceq
    #
    wo
    #
    @9
    c.0
    cX
    wceq
    #
    @36
    wo
    #
    @38
    @9
    c.0
    cX
    @35
    wbr
    #
    wn
    #
    @41
    @40
    wo
    #
    @40
    @2
    @0
    @29
    @1
    w3a
    #
    @8
    @42
    @2
    @0
    @29
    @1
    @0
    @1
    simpl
    #
    @2
    @0
    @29
    @45
    @0
    @17
    @16
    @29
    @18
    @20
    @33
    3syl
    syl
    @0
    @1
    simpr
    3jca
    @44
    @41
    @3
    corng
    cB
    cB
    @35
    cR
    c.le
    c.0
    cX
    orngmul.1
    @35
    eqid
    #
    pltle
    con3dimp
    sylan
    @9
    @41
    @39
    @36
    w3o
    #
    @43
    @9
    cB
    @35
    wor
    #
    @29
    @1
    @47
    @9
    @0
    cR
    ctos
    wcel
    #
    @48
    @15
    @0
    @28
    @49
    @32
    cR
    omndtos
    syl
    #
    @49
    @48
    cid
    cB
    cres
    c.le
    wss
    #
    @49
    @48
    @51
    wa
    cB
    @35
    cR
    c.le
    ctos
    orngmul.0
    orngmul.1
    @46
    tosso
    ibi
    simpld
    3syl
    @34
    @22
    cB
    c.0
    cX
    @35
    solin
    syl12anc
    @41
    @39
    @36
    3orass
    sylib
    @41
    @40
    orel1
    sylc
    @40
    @36
    @39
    wo
    @38
    @39
    @36
    orcom
    @39
    @37
    @36
    c.0
    cX
    eqcom
    orbi2i
    bitri
    sylib
    @9
    cR
    cpo
    wcel
    #
    @1
    @29
    @30
    @38
    wb
    @9
    @0
    @49
    @52
    @15
    @50
    cR
    tospos
    3syl
    @22
    @34
    cB
    @35
    cR
    c.le
    cX
    c.0
    orngmul.0
    orngmul.1
    @46
    pleval2
    syl3anc
    mpbird
    cB
    @25
    c.le
    cR
    cX
    c.0
    @11
    orngmul.0
    orngmul.1
    @25
    eqid
    #
    omndadd
    syl131anc
    @9
    @16
    @1
    @26
    c.0
    wceq
    @21
    @22
    cB
    @25
    cR
    @10
    cX
    c.0
    orngmul.0
    @53
    orngmul.2
    @23
    grprinv
    syl2anc
    @9
    @16
    @13
    @27
    @11
    wceq
    @21
    @24
    cB
    @25
    cR
    @11
    c.0
    orngmul.0
    @53
    orngmul.2
    grplid
    syl2anc
    3brtr3d
    #
    @24
    @54
    cB
    cR
    c.x
    c.le
    @11
    @11
    c.0
    orngmul.0
    orngmul.1
    orngmul.2
    orngmul.3
    orngmul
    syl122anc
    @9
    cB
    cR
    c.x
    @10
    cX
    cX
    orngmul.0
    orngmul.3
    @23
    @19
    @22
    @22
    ringm2neg
    breqtrd
    pm2.61dan
end
