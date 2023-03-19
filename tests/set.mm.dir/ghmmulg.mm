include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cn0.mm"
include "cfv.mm"
include "wceq.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wa.mm"
include "cmhm.mm"
include "ghmmhm.mm"
include "mhmmulg.mm"
include "syl3an1.mm"
include "3expa.mm"
include "an32s.mm"
include "3adantl2.mm"
include "cminusg.mm"
include "simpl1.mm"
include "syl.mm"
include "nnnn0.mm"
include "ad2antll.mm"
include "simpl3.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "nnz.mm"
include "mulgcl.mm"
include "eqid.mm"
include "ghminv.mm"
include "syl2anc.mm"
include "cbs.mm"
include "ghmgrp2.mm"
include "wf.mm"
include "ghmf.mm"
include "ffvelrnd.mm"
include "mulgneg.mm"
include "3eqtr4d.mm"
include "simprl.mm"
include "recnd.mm"
include "negnegd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "wo.mm"
include "simp2.mm"
include "elznn0nn.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem ghmmulg
  let cB: class B
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  assume ghmmulg.b: |- B = ( Base ` G )
  assume ghmmulg.s: |- .x. = ( .g ` G )
  assume ghmmulg.t: |- .X. = ( .g ` H )


  assert |- ( ( F e. ( G GrpHom H ) /\ N e. ZZ /\ X e. B ) -> ( F ` ( N .x. X ) ) = ( N .X. ( F ` X ) ) )

  proof
    cF
    cG
    cH
    cghm
    co
    wcel
    #
    cN
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cN
    cn0
    wcel
    #
    cN
    cX
    c.x
    co
    #
    cF
    cfv
    #
    cN
    cX
    cF
    cfv
    #
    c.xp
    co
    #
    wceq
    #
    cN
    cr
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    wa
    #
    @0
    @2
    @4
    @9
    @1
    @0
    @4
    @2
    @9
    @0
    @4
    @2
    @9
    @0
    cF
    cG
    cH
    cmhm
    co
    wcel
    #
    @4
    @2
    @9
    cG
    cH
    cF
    ghmmhm
    #
    cB
    c.x
    c.xp
    cF
    cG
    cH
    cN
    cX
    ghmmulg.b
    ghmmulg.s
    ghmmulg.t
    mhmmulg
    syl3an1
    3expa
    an32s
    3adantl2
    @3
    @13
    wa
    #
    @11
    cneg
    #
    @7
    c.xp
    co
    #
    @6
    @8
    @16
    @11
    cX
    c.x
    co
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cF
    cfv
    #
    @18
    @6
    @16
    @19
    cF
    cfv
    #
    cH
    cminusg
    cfv
    #
    cfv
    #
    @11
    @7
    c.xp
    co
    #
    @24
    cfv
    #
    @22
    @18
    @16
    @23
    @26
    @24
    @16
    @14
    @11
    cn0
    wcel
    #
    @2
    @23
    @26
    wceq
    @16
    @0
    @14
    @0
    @1
    @2
    @13
    simpl1
    #
    @15
    syl
    @12
    @28
    @3
    @10
    @11
    nnnn0
    ad2antll
    @0
    @1
    @2
    @13
    simpl3
    #
    cB
    c.x
    c.xp
    cF
    cG
    cH
    @11
    cX
    ghmmulg.b
    ghmmulg.s
    ghmmulg.t
    mhmmulg
    syl3anc
    fveq2d
    @16
    @0
    @19
    cB
    wcel
    #
    @22
    @25
    wceq
    @29
    @16
    cG
    cgrp
    wcel
    #
    @11
    cz
    wcel
    #
    @2
    @31
    @16
    @0
    @32
    @29
    cG
    cH
    cF
    ghmgrp1
    syl
    #
    @12
    @33
    @3
    @10
    @11
    nnz
    ad2antll
    #
    @30
    cB
    c.x
    cG
    @11
    cX
    ghmmulg.b
    ghmmulg.s
    mulgcl
    syl3anc
    cB
    cG
    cH
    cF
    @20
    @24
    @19
    ghmmulg.b
    @20
    eqid
    #
    @24
    eqid
    #
    ghminv
    syl2anc
    @16
    cH
    cgrp
    wcel
    #
    @33
    @7
    cH
    cbs
    cfv
    #
    wcel
    @18
    @27
    wceq
    @16
    @0
    @38
    @29
    cG
    cH
    cF
    ghmgrp2
    syl
    @35
    @16
    cB
    @39
    cX
    cF
    @16
    @0
    cB
    @39
    cF
    wf
    @29
    cG
    cH
    cF
    cB
    @39
    ghmmulg.b
    @39
    eqid
    #
    ghmf
    syl
    @30
    ffvelrnd
    @39
    c.xp
    cH
    @24
    @11
    @7
    @40
    ghmmulg.t
    @37
    mulgneg
    syl3anc
    3eqtr4d
    @16
    @21
    @5
    cF
    @16
    @17
    cX
    c.x
    co
    #
    @21
    @5
    @16
    @32
    @33
    @2
    @41
    @21
    wceq
    @34
    @35
    @30
    cB
    c.x
    cG
    @20
    @11
    cX
    ghmmulg.b
    ghmmulg.s
    @36
    mulgneg
    syl3anc
    @16
    @17
    cN
    cX
    c.x
    @16
    cN
    @16
    cN
    @3
    @10
    @12
    simprl
    recnd
    negnegd
    #
    oveq1d
    eqtr3d
    fveq2d
    eqtr3d
    @16
    @17
    cN
    @7
    c.xp
    @42
    oveq1d
    eqtr3d
    @3
    @1
    @4
    @13
    wo
    @0
    @1
    @2
    simp2
    cN
    elznn0nn
    sylib
    mpjaodan
end
