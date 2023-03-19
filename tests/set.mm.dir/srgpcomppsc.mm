include "co.mm"
include "c1.mm"
include "caddc.mm"
include "csrg.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "cmnd.mm"
include "srgmgp.mm"
include "syl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "w3a.mm"
include "wa.mm"
include "srgmulgass.mm"
include "eqcomd.mm"
include "syl13anc.mm"
include "oveq1d.mm"
include "srgmnd.mm"
include "srgass.mm"
include "eqtrd.mm"
include "srgcl.mm"
include "oveq2d.mm"
include "srgpcompp.mm"
include "3eqtrd.mm"

theorem srgpcomppsc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let c.ex: class .^
  let cG: class G
  let cK: class K
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume srgpcomp.s: |- S = ( Base ` R )
  assume srgpcomp.m: |- .X. = ( .r ` R )
  assume srgpcomp.g: |- G = ( mulGrp ` R )
  assume srgpcomp.e: |- .^ = ( .g ` G )
  assume srgpcomp.r: |- ( ph -> R e. SRing )
  assume srgpcomp.a: |- ( ph -> A e. S )
  assume srgpcomp.b: |- ( ph -> B e. S )
  assume srgpcomp.k: |- ( ph -> K e. NN0 )
  assume srgpcomp.c: |- ( ph -> ( A .X. B ) = ( B .X. A ) )
  assume srgpcompp.n: |- ( ph -> N e. NN0 )
  assume srgpcomppsc.t: |- .x. = ( .g ` R )
  assume srgpcomppsc.c: |- ( ph -> C e. NN0 )


  assert |- ( ph -> ( ( C .x. ( ( N .^ A ) .X. ( K .^ B ) ) ) .X. A ) = ( C .x. ( ( ( N + 1 ) .^ A ) .X. ( K .^ B ) ) ) )

  proof
    wph
    cC
    cN
    cA
    c.ex
    co
    #
    cK
    cB
    c.ex
    co
    #
    c.xp
    co
    #
    c.x
    co
    #
    cA
    c.xp
    co
    #
    cC
    @0
    c.x
    co
    #
    @1
    cA
    c.xp
    co
    #
    c.xp
    co
    #
    cC
    @2
    cA
    c.xp
    co
    #
    c.x
    co
    #
    cC
    cN
    c1
    caddc
    co
    cA
    c.ex
    co
    @1
    c.xp
    co
    #
    c.x
    co
    wph
    @4
    @5
    @1
    c.xp
    co
    #
    cA
    c.xp
    co
    #
    @7
    wph
    @3
    @11
    cA
    c.xp
    wph
    cR
    csrg
    wcel
    #
    cC
    cn0
    wcel
    #
    @0
    cS
    wcel
    #
    @1
    cS
    wcel
    #
    @3
    @11
    wceq
    srgpcomp.r
    srgpcomppsc.c
    wph
    cG
    cmnd
    wcel
    #
    cN
    cn0
    wcel
    cA
    cS
    wcel
    #
    @15
    wph
    @13
    @17
    srgpcomp.r
    cR
    cG
    srgpcomp.g
    srgmgp
    syl
    #
    srgpcompp.n
    srgpcomp.a
    cS
    c.ex
    cG
    cN
    cA
    cS
    cR
    cG
    srgpcomp.g
    srgpcomp.s
    mgpbas
    #
    srgpcomp.e
    mulgnn0cl
    syl3anc
    #
    wph
    @17
    cK
    cn0
    wcel
    cB
    cS
    wcel
    @16
    @19
    srgpcomp.k
    srgpcomp.b
    cS
    c.ex
    cG
    cK
    cB
    @20
    srgpcomp.e
    mulgnn0cl
    syl3anc
    #
    @13
    @14
    @15
    @16
    w3a
    wa
    @11
    @3
    cS
    cR
    c.x
    c.xp
    cC
    @0
    @1
    srgpcomp.s
    srgpcomppsc.t
    srgpcomp.m
    srgmulgass
    eqcomd
    syl13anc
    oveq1d
    wph
    @13
    @5
    cS
    wcel
    #
    @16
    @18
    @12
    @7
    wceq
    srgpcomp.r
    wph
    cR
    cmnd
    wcel
    #
    @14
    @15
    @23
    wph
    @13
    @24
    srgpcomp.r
    cR
    srgmnd
    syl
    srgpcomppsc.c
    @21
    cS
    c.x
    cR
    cC
    @0
    srgpcomp.s
    srgpcomppsc.t
    mulgnn0cl
    syl3anc
    @22
    srgpcomp.a
    cS
    cR
    c.xp
    @5
    @1
    cA
    srgpcomp.s
    srgpcomp.m
    srgass
    syl13anc
    eqtrd
    wph
    @7
    cC
    @0
    @6
    c.xp
    co
    #
    c.x
    co
    #
    @9
    wph
    @13
    @14
    @15
    @6
    cS
    wcel
    #
    @7
    @26
    wceq
    srgpcomp.r
    srgpcomppsc.c
    @21
    wph
    @13
    @16
    @18
    @27
    srgpcomp.r
    @22
    srgpcomp.a
    cS
    cR
    c.xp
    @1
    cA
    srgpcomp.s
    srgpcomp.m
    srgcl
    syl3anc
    cS
    cR
    c.x
    c.xp
    cC
    @0
    @6
    srgpcomp.s
    srgpcomppsc.t
    srgpcomp.m
    srgmulgass
    syl13anc
    wph
    @25
    @8
    cC
    c.x
    wph
    @8
    @25
    wph
    @13
    @15
    @16
    @18
    @8
    @25
    wceq
    srgpcomp.r
    @21
    @22
    srgpcomp.a
    cS
    cR
    c.xp
    @0
    @1
    cA
    srgpcomp.s
    srgpcomp.m
    srgass
    syl13anc
    eqcomd
    oveq2d
    eqtrd
    wph
    @8
    @10
    cC
    c.x
    wph
    cA
    cB
    cR
    cS
    c.xp
    c.ex
    cG
    cK
    cN
    srgpcomp.s
    srgpcomp.m
    srgpcomp.g
    srgpcomp.e
    srgpcomp.r
    srgpcomp.a
    srgpcomp.b
    srgpcomp.k
    srgpcomp.c
    srgpcompp.n
    srgpcompp
    oveq2d
    3eqtrd
end
