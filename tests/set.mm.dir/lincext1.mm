include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "wf.mm"
include "cgrp.mm"
include "csca.mm"
include "eqid.mm"
include "lmodfgrp.mm"
include "ad2antrr.mm"
include "syl5eqel.mm"
include "simpr1.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "wn.mm"
include "wi.mm"
include "elmapi.mm"
include "wne.mm"
include "df-ne.mm"
include "biimpri.mm"
include "anim2i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "ffvelrn.mm"
include "sylan2.mm"
include "ex.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "impl.mm"
include "ifclda.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "simpr.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "jctil.mm"
include "adantr.mm"
include "elmapg.mm"
include "mpbird.mm"

theorem lincext1
  let vz: setvar z
  let cB: class B
  let cR: class R
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume lincext.b: |- B = ( Base ` M )
  assume lincext.r: |- R = ( Scalar ` M )
  assume lincext.e: |- E = ( Base ` R )
  assume lincext.0: |- .0. = ( 0g ` R )
  assume lincext.z: |- Z = ( 0g ` M )
  assume lincext.n: |- N = ( invg ` R )
  assume lincext.f: |- F = ( z e. S |-> if ( z = X , ( N ` Y ) , ( G ` z ) ) )

  disjoint B z
  disjoint E z
  disjoint G z
  disjoint M z
  disjoint S z
  disjoint X z
  disjoint Y z
  disjoint k x
  assert |- ( ( ( M e. LMod /\ S e. ~P B ) /\ ( Y e. E /\ X e. S /\ G e. ( E ^m ( S \ { X } ) ) ) ) -> F e. ( E ^m S ) )

  proof
    cM
    clmod
    wcel
    #
    cS
    cB
    cpw
    #
    wcel
    #
    wa
    #
    cY
    cE
    wcel
    #
    cX
    cS
    wcel
    #
    cG
    cE
    cS
    cX
    csn
    cdif
    #
    cmap
    co
    wcel
    #
    w3a
    #
    wa
    #
    cF
    vz
    cS
    vz
    cv
    #
    cX
    wceq
    #
    cY
    cN
    cfv
    #
    @10
    cG
    cfv
    #
    cif
    #
    cmpt
    #
    cE
    cS
    cmap
    co
    #
    lincext.f
    @9
    @15
    @16
    wcel
    #
    cS
    cE
    @15
    wf
    #
    @9
    vz
    cS
    @14
    cE
    @15
    @9
    @10
    cS
    wcel
    #
    wa
    @11
    @12
    @13
    cE
    @9
    @12
    cE
    wcel
    #
    @19
    @11
    @9
    cR
    cgrp
    wcel
    @4
    @20
    @9
    cR
    cM
    csca
    cfv
    #
    cgrp
    lincext.r
    @0
    @21
    cgrp
    wcel
    @2
    @8
    @21
    cM
    @21
    eqid
    lmodfgrp
    ad2antrr
    syl5eqel
    @3
    @4
    @5
    @7
    simpr1
    cE
    cR
    cN
    cY
    lincext.e
    lincext.n
    grpinvcl
    syl2anc
    ad2antrr
    @9
    @19
    @11
    wn
    #
    @13
    cE
    wcel
    #
    @8
    @19
    @22
    wa
    #
    @23
    wi
    #
    @3
    @7
    @4
    @25
    @5
    @7
    @6
    cE
    cG
    wf
    #
    @25
    cG
    cE
    @6
    elmapi
    @26
    @24
    @23
    @24
    @26
    @10
    @6
    wcel
    #
    @23
    @24
    @19
    @10
    cX
    wne
    #
    wa
    @27
    @22
    @28
    @19
    @28
    @22
    @10
    cX
    df-ne
    biimpri
    anim2i
    @10
    cS
    cX
    eldifsn
    sylibr
    @6
    cE
    @10
    cG
    ffvelrn
    sylan2
    ex
    syl
    3ad2ant3
    adantl
    impl
    ifclda
    @15
    eqid
    fmptd
    @9
    cE
    cvv
    wcel
    #
    @2
    wa
    #
    @17
    @18
    wb
    @3
    @30
    @8
    @3
    @2
    @29
    @0
    @2
    simpr
    cE
    cR
    cbs
    cfv
    cvv
    lincext.e
    cR
    cbs
    fvex
    eqeltri
    jctil
    adantr
    cE
    cS
    @15
    cvv
    @1
    elmapg
    syl
    mpbird
    syl5eqel
end
