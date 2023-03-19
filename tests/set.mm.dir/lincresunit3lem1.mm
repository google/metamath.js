include "cpw.mm"
include "wcel.mm"
include "clmod.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "cvsca.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "adantl.mm"
include "simpr3.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "oveq1d.mm"
include "simp2.mm"
include "adantr.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "3ad2ant2.mm"
include "unitcl.mm"
include "grpinvcl.mm"
include "syl2an.mm"
include "3simpa.mm"
include "anim2i.mm"
include "eldifi.mm"
include "3ad2ant3.mm"
include "lincresunitlem2.mm"
include "syl2anc.mm"
include "wi.mm"
include "elpwi.mm"
include "sseld.mm"
include "syl5com.mm"
include "com12.mm"
include "3ad2ant1.mm"
include "imp.mm"
include "eqid.mm"
include "lmodvsass.mm"
include "eqcomd.mm"
include "syl13anc.mm"
include "crg.mm"
include "lmodring.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "3adant2.mm"
include "invginvrid.mm"
include "syl3anc.mm"
include "3eqtrd.mm"

theorem lincresunit3lem1
  let vz: setvar z
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume lincresunit.b: |- B = ( Base ` M )
  assume lincresunit.r: |- R = ( Scalar ` M )
  assume lincresunit.e: |- E = ( Base ` R )
  assume lincresunit.u: |- U = ( Unit ` R )
  assume lincresunit.0: |- .0. = ( 0g ` R )
  assume lincresunit.z: |- Z = ( 0g ` M )
  assume lincresunit.n: |- N = ( invg ` R )
  assume lincresunit.i: |- I = ( invr ` R )
  assume lincresunit.t: |- .x. = ( .r ` R )
  assume lincresunit.g: |- G = ( s e. ( S \ { X } ) |-> ( ( I ` ( N ` ( F ` X ) ) ) .x. ( F ` s ) ) )

  disjoint B s
  disjoint E s
  disjoint F s
  disjoint M s
  disjoint S s
  disjoint X s
  disjoint U s
  disjoint I s
  disjoint N s
  disjoint .x. s
  disjoint s z
  disjoint k x
  assert |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S ) /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U /\ z e. ( S \ { X } ) ) ) -> ( ( N ` ( F ` X ) ) ( .s ` M ) ( ( G ` z ) ( .s ` M ) z ) ) = ( ( F ` z ) ( .s ` M ) z ) )

  proof
    cS
    cB
    cpw
    wcel
    #
    cM
    clmod
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cF
    cE
    cS
    cmap
    co
    wcel
    #
    cX
    cF
    cfv
    #
    cU
    wcel
    #
    vz
    cv
    #
    cS
    cX
    csn
    #
    cdif
    #
    wcel
    #
    w3a
    #
    wa
    #
    @5
    cN
    cfv
    #
    @7
    cG
    cfv
    #
    @7
    cM
    cvsca
    cfv
    #
    co
    #
    @15
    co
    @13
    @13
    cI
    cfv
    #
    @7
    cF
    cfv
    #
    c.x
    co
    #
    @7
    @15
    co
    #
    @15
    co
    #
    @13
    @19
    c.x
    co
    #
    @7
    @15
    co
    #
    @18
    @7
    @15
    co
    @12
    @16
    @20
    @13
    @15
    @12
    @14
    @19
    @7
    @15
    @12
    vs
    @7
    @17
    vs
    cv
    #
    cF
    cfv
    #
    c.x
    co
    #
    @19
    @9
    cG
    cvv
    cG
    vs
    @9
    @26
    cmpt
    wceq
    @12
    lincresunit.g
    a1i
    vs
    vz
    weq
    #
    @26
    @19
    wceq
    @12
    @27
    @25
    @18
    @17
    c.x
    @24
    @7
    cF
    fveq2
    oveq2d
    adantl
    @3
    @4
    @6
    @10
    simpr3
    @12
    @17
    @18
    c.x
    ovexd
    fvmptd
    oveq1d
    oveq2d
    @12
    @1
    @13
    cE
    wcel
    #
    @19
    cE
    wcel
    #
    @7
    cB
    wcel
    #
    @21
    @23
    wceq
    @3
    @1
    @11
    @0
    @1
    @2
    simp2
    adantr
    @3
    cR
    cgrp
    wcel
    #
    @5
    cE
    wcel
    #
    @28
    @11
    @1
    @0
    @31
    @2
    cR
    cM
    lincresunit.r
    lmodfgrp
    3ad2ant2
    @6
    @4
    @32
    @10
    cE
    cR
    cU
    @5
    lincresunit.e
    lincresunit.u
    unitcl
    3ad2ant2
    cE
    cR
    cN
    @5
    lincresunit.e
    lincresunit.n
    grpinvcl
    syl2an
    @12
    @3
    @4
    @6
    wa
    #
    wa
    @7
    cS
    wcel
    #
    @29
    @11
    @33
    @3
    @4
    @6
    @10
    3simpa
    anim2i
    @11
    @34
    @3
    @10
    @4
    @34
    @6
    @7
    cS
    @8
    eldifi
    #
    3ad2ant3
    adantl
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    @7
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunitlem2
    syl2anc
    @3
    @11
    @30
    @0
    @1
    @11
    @30
    wi
    @2
    @11
    @0
    @30
    @10
    @4
    @0
    @30
    wi
    @6
    @10
    @34
    @0
    @30
    @35
    @0
    cS
    cB
    @7
    cS
    cB
    elpwi
    sseld
    syl5com
    3ad2ant3
    com12
    3ad2ant1
    imp
    @1
    @28
    @29
    @30
    w3a
    wa
    @23
    @21
    @13
    @19
    @15
    c.x
    cR
    cE
    cB
    cM
    @7
    lincresunit.b
    lincresunit.r
    @15
    eqid
    lincresunit.e
    lincresunit.t
    lmodvsass
    eqcomd
    syl13anc
    @12
    @22
    @18
    @7
    @15
    @12
    cR
    crg
    wcel
    #
    @18
    cE
    wcel
    #
    @6
    @22
    @18
    wceq
    @3
    @36
    @11
    @1
    @0
    @36
    @2
    cR
    cM
    lincresunit.r
    lmodring
    3ad2ant2
    adantr
    @11
    @37
    @3
    @4
    @10
    @37
    @6
    @4
    cS
    cE
    cF
    wf
    @34
    @37
    @10
    cF
    cE
    cS
    elmapi
    @35
    cS
    cE
    @7
    cF
    ffvelrn
    syl2an
    3adant2
    adantl
    @11
    @6
    @3
    @4
    @6
    @10
    simp2
    adantl
    cE
    cR
    c.x
    cU
    cI
    cN
    @18
    @5
    lincresunit.e
    lincresunit.u
    lincresunit.n
    lincresunit.i
    lincresunit.t
    invginvrid
    syl3anc
    oveq1d
    3eqtrd
end
