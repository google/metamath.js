include "cidom.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "chash.mm"
include "cmgp.mm"
include "cmg.mm"
include "co.mm"
include "cur.mm"
include "wceq.mm"
include "cbs.mm"
include "cvv.mm"
include "cxr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "hashxrcl.mm"
include "mp1i.mm"
include "nnre.mm"
include "rexrd.mm"
include "adantl.mm"
include "cle.mm"
include "c0g.mm"
include "cgrp.mm"
include "cz.mm"
include "wb.mm"
include "crg.mm"
include "ccrg.mm"
include "cdomn.mm"
include "isidom.mm"
include "simplbi.mm"
include "adantr.mm"
include "crngring.mm"
include "syl.mm"
include "cui.mm"
include "eqid.mm"
include "unitgrp.mm"
include "simpr.mm"
include "nnz.mm"
include "ad2antlr.mm"
include "oddvds.mm"
include "syl3anc.mm"
include "csubmnd.mm"
include "cn0.mm"
include "unitsubm.mm"
include "nnnn0.mm"
include "unitgrpbas.mm"
include "eqtr4i.mm"
include "syl6eleq.mm"
include "submmulg.mm"
include "unitgrpid.mm"
include "eqeq12d.mm"
include "bitr4d.mm"
include "rabbidva.mm"
include "fveq2d.mm"
include "cdom.mm"
include "wss.mm"
include "unitss.mm"
include "rabss2.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "hashdomi.mm"
include "eqbrtrd.mm"
include "simpl.mm"
include "ringidcl.mm"
include "idomrootle.mm"
include "xrletrd.mm"

theorem idomodle
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cG: class G
  let cN: class N
  let cO: class O
  assume idomodle.g: |- G = ( ( mulGrp ` R ) |`s ( Unit ` R ) )
  assume idomodle.b: |- B = ( Base ` G )
  assume idomodle.o: |- O = ( od ` G )

  disjoint B x
  disjoint N x
  disjoint R x
  assert |- ( ( R e. IDomn /\ N e. NN ) -> ( # ` { x e. B | ( O ` x ) || N } ) <_ N )

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
    vx
    cv
    #
    cO
    cfv
    cN
    cdvds
    wbr
    #
    vx
    cB
    crab
    #
    chash
    cfv
    #
    cN
    @3
    cR
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    cR
    cur
    cfv
    #
    wceq
    #
    vx
    cR
    cbs
    cfv
    #
    crab
    #
    chash
    cfv
    #
    cN
    @5
    cvv
    wcel
    @6
    cxr
    wcel
    @2
    @4
    vx
    cB
    cB
    cG
    cbs
    cfv
    #
    cvv
    idomodle.b
    cG
    cbs
    fvex
    eqeltri
    rabex
    @5
    cvv
    hashxrcl
    mp1i
    @13
    cvv
    wcel
    #
    @14
    cxr
    wcel
    @2
    @11
    vx
    @12
    cR
    cbs
    fvex
    rabex
    #
    @13
    cvv
    hashxrcl
    mp1i
    @1
    cN
    cxr
    wcel
    @0
    @1
    cN
    cN
    nnre
    rexrd
    adantl
    @2
    @6
    @11
    vx
    cB
    crab
    #
    chash
    cfv
    #
    @14
    cle
    @2
    @5
    @18
    chash
    @2
    @4
    @11
    vx
    cB
    @2
    @3
    cB
    wcel
    #
    wa
    #
    @4
    cN
    @3
    cG
    cmg
    cfv
    #
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    @11
    @21
    cG
    cgrp
    wcel
    #
    @20
    cN
    cz
    wcel
    #
    @4
    @25
    wb
    @21
    cR
    crg
    wcel
    #
    @26
    @2
    @28
    @20
    @2
    cR
    ccrg
    wcel
    #
    @28
    @0
    @29
    @1
    @0
    @29
    cR
    cdomn
    wcel
    cR
    isidom
    simplbi
    adantr
    cR
    crngring
    syl
    #
    adantr
    #
    cR
    cR
    cui
    cfv
    #
    cG
    @32
    eqid
    #
    idomodle.g
    unitgrp
    syl
    @2
    @20
    simpr
    #
    @1
    @27
    @0
    @20
    cN
    nnz
    ad2antlr
    @3
    @22
    cG
    cN
    cO
    cB
    @24
    idomodle.b
    idomodle.o
    @22
    eqid
    #
    @24
    eqid
    oddvds
    syl3anc
    @21
    @9
    @23
    @10
    @24
    @21
    @32
    @7
    csubmnd
    cfv
    wcel
    #
    cN
    cn0
    wcel
    #
    @3
    @32
    wcel
    @9
    @23
    wceq
    @21
    @28
    @36
    @31
    cR
    @32
    @7
    @33
    @7
    eqid
    unitsubm
    syl
    @1
    @37
    @0
    @20
    cN
    nnnn0
    ad2antlr
    @21
    @3
    cB
    @32
    @34
    cB
    @15
    @32
    idomodle.b
    cR
    @32
    cG
    @33
    idomodle.g
    unitgrpbas
    eqtr4i
    #
    syl6eleq
    @32
    @8
    @22
    @7
    cG
    cN
    @3
    @8
    eqid
    #
    idomodle.g
    @35
    submmulg
    syl3anc
    @21
    @28
    @10
    @24
    wceq
    @31
    cR
    @32
    @10
    cG
    @33
    idomodle.g
    @10
    eqid
    #
    unitgrpid
    syl
    eqeq12d
    bitr4d
    rabbidva
    fveq2d
    @2
    @18
    @13
    cdom
    wbr
    #
    @19
    @14
    cle
    wbr
    @16
    @2
    @18
    @13
    wss
    #
    @41
    @17
    cB
    @12
    wss
    @42
    @2
    @12
    cR
    cB
    @12
    eqid
    #
    @38
    unitss
    @11
    vx
    cB
    @12
    rabss2
    mp1i
    @18
    @13
    cvv
    ssdomg
    mpsyl
    @18
    @13
    hashdomi
    syl
    eqbrtrd
    @2
    @0
    @10
    @12
    wcel
    #
    @1
    @14
    cN
    cle
    wbr
    @0
    @1
    simpl
    @2
    @28
    @44
    @30
    @12
    cR
    @10
    @43
    @40
    ringidcl
    syl
    @0
    @1
    simpr
    vx
    @12
    cR
    @8
    cN
    @10
    @43
    @39
    idomrootle
    syl3anc
    xrletrd
end
