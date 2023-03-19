include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "cn.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cmo.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cneg.mm"
include "cplusg.mm"
include "cmin.mm"
include "caddc.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "nnrp.mm"
include "modval.mm"
include "syl2an.mm"
include "3ad2ant2.mm"
include "oveq1d.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "nnz.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "nnre.mm"
include "nnne0.mm"
include "redivcl.mm"
include "syl3an.mm"
include "3anidm23.mm"
include "flcld.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "negsubd.mm"
include "simp1.mm"
include "simpl.mm"
include "znegcld.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "3eqtr2d.mm"
include "nncn.mm"
include "mulneg2d.mm"
include "mulgassr.mm"
include "oveq2.mm"
include "mulgz.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "id.mm"
include "mulgcl.mm"
include "grprid.mm"

theorem mulgmodid
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume mulgmodid.b: |- B = ( Base ` G )
  assume mulgmodid.o: |- .0. = ( 0g ` G )
  assume mulgmodid.t: |- .x. = ( .g ` G )


  assert |- ( ( G e. Grp /\ ( N e. ZZ /\ M e. NN ) /\ ( X e. B /\ ( M .x. X ) = .0. ) ) -> ( ( N mod M ) .x. X ) = ( N .x. X ) )

  proof
    cG
    cgrp
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cn
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cM
    cX
    c.x
    co
    #
    c.0
    wceq
    #
    wa
    #
    w3a
    #
    cN
    cM
    cmo
    co
    #
    cX
    c.x
    co
    #
    cN
    cX
    c.x
    co
    #
    cM
    cN
    cM
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cneg
    #
    cX
    c.x
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @11
    c.0
    @17
    co
    #
    @11
    @8
    @10
    cN
    @14
    cmin
    co
    #
    cX
    c.x
    co
    cN
    @15
    caddc
    co
    #
    cX
    c.x
    co
    #
    @18
    @8
    @9
    @20
    cX
    c.x
    @3
    @0
    @9
    @20
    wceq
    #
    @7
    @1
    cN
    cr
    wcel
    #
    cM
    crp
    wcel
    @23
    @2
    cN
    zre
    #
    cM
    nnrp
    cN
    cM
    modval
    syl2an
    3ad2ant2
    oveq1d
    @8
    @21
    @20
    cX
    c.x
    @3
    @0
    @21
    @20
    wceq
    @7
    @3
    cN
    @14
    @1
    cN
    cc
    wcel
    @2
    cN
    zcn
    adantr
    @3
    @14
    @3
    cM
    @13
    @2
    cM
    cz
    wcel
    #
    @1
    cM
    nnz
    adantl
    #
    @3
    @12
    @1
    @2
    @12
    cr
    wcel
    #
    @1
    @24
    @2
    cM
    cr
    wcel
    @2
    cM
    cc0
    wne
    @28
    @25
    cM
    nnre
    cM
    nnne0
    cN
    cM
    redivcl
    syl3an
    3anidm23
    #
    flcld
    #
    zmulcld
    zcnd
    negsubd
    3ad2ant2
    oveq1d
    @8
    @0
    @1
    @15
    cz
    wcel
    @4
    @22
    @18
    wceq
    @0
    @3
    @7
    simp1
    #
    @3
    @0
    @1
    @7
    @1
    @2
    simpl
    #
    3ad2ant2
    @8
    @14
    @8
    cM
    @13
    @3
    @0
    @26
    @7
    @27
    3ad2ant2
    #
    @3
    @0
    @13
    cz
    wcel
    @7
    @30
    3ad2ant2
    zmulcld
    znegcld
    @7
    @0
    @4
    @3
    @4
    @6
    simpl
    #
    3ad2ant3
    #
    cB
    @17
    c.x
    cG
    cN
    @15
    cX
    mulgmodid.b
    mulgmodid.t
    @17
    eqid
    #
    mulgdir
    syl13anc
    3eqtr2d
    @8
    @16
    c.0
    @11
    @17
    @8
    cM
    @13
    cneg
    #
    cmul
    co
    #
    cX
    c.x
    co
    #
    @16
    c.0
    @8
    @38
    @15
    cX
    c.x
    @3
    @0
    @38
    @15
    wceq
    @7
    @3
    cM
    @13
    @2
    cM
    cc
    wcel
    @1
    cM
    nncn
    adantl
    @3
    @13
    @30
    zcnd
    mulneg2d
    3ad2ant2
    oveq1d
    @8
    @39
    @37
    @5
    c.x
    co
    #
    @37
    c.0
    c.x
    co
    #
    c.0
    @8
    @0
    @37
    cz
    wcel
    #
    @26
    @4
    @39
    @40
    wceq
    @31
    @8
    @13
    @8
    @12
    @3
    @0
    @28
    @7
    @29
    3ad2ant2
    flcld
    znegcld
    #
    @33
    @35
    cB
    c.x
    cG
    @37
    cM
    cX
    mulgmodid.b
    mulgmodid.t
    mulgassr
    syl13anc
    @7
    @0
    @40
    @41
    wceq
    #
    @3
    @6
    @44
    @4
    @5
    c.0
    @37
    c.x
    oveq2
    adantl
    3ad2ant3
    @8
    @0
    @42
    @41
    c.0
    wceq
    @31
    @43
    cB
    c.x
    cG
    @37
    c.0
    mulgmodid.b
    mulgmodid.t
    mulgmodid.o
    mulgz
    syl2anc
    3eqtrd
    eqtr3d
    oveq2d
    @8
    @0
    @11
    cB
    wcel
    #
    @19
    @11
    wceq
    @31
    @0
    @0
    @3
    @1
    @7
    @4
    @45
    @0
    id
    @32
    @34
    cB
    c.x
    cG
    cN
    cX
    mulgmodid.b
    mulgmodid.t
    mulgcl
    syl3an
    cB
    @17
    cG
    @11
    c.0
    mulgmodid.b
    @36
    mulgmodid.o
    grprid
    syl2anc
    3eqtrd
end
