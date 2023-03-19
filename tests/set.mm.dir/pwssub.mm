include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cof.mm"
include "cbs.mm"
include "cvv.mm"
include "simplr.mm"
include "eqid.mm"
include "simpll.mm"
include "simprl.mm"
include "pwselbas.mm"
include "ffvelrnda.mm"
include "fvexd.mm"
include "feqmptd.mm"
include "ccom.mm"
include "wceq.mm"
include "simprr.mm"
include "pwsinvg.mm"
include "syl3anc.mm"
include "wf.mm"
include "grpinvf.mm"
include "ad2antrr.mm"
include "fveq2.mm"
include "fmptco.mm"
include "eqtrd.mm"
include "offval2.mm"
include "pwsgrp.mm"
include "adantr.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "pwsplusgval.mm"
include "grpsubval.mm"
include "mpteq2dva.mm"
include "3eqtr4d.mm"
include "adantl.mm"

theorem pwssub
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let c.mi: class .-
  let cV: class V
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cN: class N
  assume pwsgrp.y: |- Y = ( R ^s I )
  assume pwsinvg.b: |- B = ( Base ` Y )
  assume pwssub.m: |- M = ( -g ` R )
  assume pwssub.n: |- .- = ( -g ` Y )


  assert |- ( ( ( R e. Grp /\ I e. V ) /\ ( F e. B /\ G e. B ) ) -> ( F .- G ) = ( F oF M G ) )

  proof
    cR
    cgrp
    wcel
    #
    cI
    cV
    wcel
    #
    wa
    #
    cF
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    wa
    #
    wa
    #
    cF
    cG
    cY
    cminusg
    cfv
    #
    cfv
    #
    cY
    cplusg
    cfv
    #
    co
    #
    vx
    cI
    vx
    cv
    #
    cF
    cfv
    #
    @11
    cG
    cfv
    #
    cM
    co
    #
    cmpt
    #
    cF
    cG
    c.mi
    co
    #
    cF
    cG
    cM
    cof
    co
    @6
    cF
    @8
    cR
    cplusg
    cfv
    #
    cof
    co
    vx
    cI
    @12
    @13
    cR
    cminusg
    cfv
    #
    cfv
    #
    @17
    co
    #
    cmpt
    @10
    @15
    @6
    vx
    cI
    @12
    @19
    @17
    cF
    @8
    cV
    cR
    cbs
    cfv
    #
    cvv
    @0
    @1
    @5
    simplr
    #
    @6
    cI
    @21
    @11
    cF
    @6
    @21
    cR
    cI
    cB
    cgrp
    cF
    cY
    cV
    pwsgrp.y
    @21
    eqid
    #
    pwsinvg.b
    @0
    @1
    @5
    simpll
    #
    @22
    @2
    @3
    @4
    simprl
    #
    pwselbas
    #
    ffvelrnda
    #
    @6
    @11
    cI
    wcel
    wa
    #
    @13
    @18
    fvexd
    @6
    vx
    cI
    @21
    cF
    @26
    feqmptd
    #
    @6
    @8
    @18
    cG
    ccom
    #
    vx
    cI
    @19
    cmpt
    @6
    @0
    @1
    @4
    @8
    @30
    wceq
    @24
    @22
    @2
    @3
    @4
    simprr
    #
    cB
    cR
    cI
    @18
    @7
    cV
    cG
    cY
    pwsgrp.y
    pwsinvg.b
    @18
    eqid
    #
    @7
    eqid
    #
    pwsinvg
    syl3anc
    @6
    vx
    vy
    cI
    @21
    @13
    vy
    cv
    #
    @18
    cfv
    @19
    cG
    @18
    @6
    cI
    @21
    @11
    cG
    @6
    @21
    cR
    cI
    cB
    cgrp
    cG
    cY
    cV
    pwsgrp.y
    @23
    pwsinvg.b
    @24
    @22
    @31
    pwselbas
    #
    ffvelrnda
    #
    @6
    vx
    cI
    @21
    cG
    @35
    feqmptd
    #
    @6
    vy
    @21
    @21
    @18
    @0
    @21
    @21
    @18
    wf
    @1
    @5
    @21
    cR
    @18
    @23
    @32
    grpinvf
    ad2antrr
    feqmptd
    @34
    @13
    @18
    fveq2
    fmptco
    eqtrd
    offval2
    @6
    cB
    @17
    @9
    cR
    cF
    @8
    cI
    cgrp
    cV
    cY
    pwsgrp.y
    pwsinvg.b
    @24
    @22
    @25
    @6
    cY
    cgrp
    wcel
    #
    @4
    @8
    cB
    wcel
    @2
    @38
    @5
    cR
    cI
    cV
    cY
    pwsgrp.y
    pwsgrp
    adantr
    @31
    cB
    cY
    @7
    cG
    pwsinvg.b
    @33
    grpinvcl
    syl2anc
    @17
    eqid
    #
    @9
    eqid
    #
    pwsplusgval
    @6
    vx
    cI
    @14
    @20
    @28
    @12
    @21
    wcel
    @13
    @21
    wcel
    @14
    @20
    wceq
    @27
    @36
    @21
    @17
    cR
    @18
    cM
    @12
    @13
    @23
    @39
    @32
    pwssub.m
    grpsubval
    syl2anc
    mpteq2dva
    3eqtr4d
    @5
    @16
    @10
    wceq
    @2
    cB
    @9
    cY
    @7
    c.mi
    cF
    cG
    pwsinvg.b
    @40
    @33
    pwssub.n
    grpsubval
    adantl
    @6
    vx
    cI
    @12
    @13
    cM
    cF
    cG
    cV
    @21
    @21
    @22
    @27
    @36
    @29
    @37
    offval2
    3eqtr4d
end
