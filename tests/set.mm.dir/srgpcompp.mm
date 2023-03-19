include "co.mm"
include "c1.mm"
include "caddc.mm"
include "csrg.mm"
include "wcel.mm"
include "wceq.mm"
include "cmnd.mm"
include "cn0.mm"
include "srgmgp.mm"
include "syl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "srgass.mm"
include "syl13anc.mm"
include "srgpcomp.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "mgpplusg.mm"
include "mulgnn0p1.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem srgpcompp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
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


  assert |- ( ph -> ( ( ( N .^ A ) .X. ( K .^ B ) ) .X. A ) = ( ( ( N + 1 ) .^ A ) .X. ( K .^ B ) ) )

  proof
    wph
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
    cA
    c.xp
    co
    #
    @0
    @1
    cA
    c.xp
    co
    #
    c.xp
    co
    #
    @0
    cA
    c.xp
    co
    #
    @1
    c.xp
    co
    #
    cN
    c1
    caddc
    co
    cA
    c.ex
    co
    #
    @1
    c.xp
    co
    wph
    cR
    csrg
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
    cA
    cS
    wcel
    #
    @2
    @4
    wceq
    srgpcomp.r
    wph
    cG
    cmnd
    wcel
    #
    cN
    cn0
    wcel
    #
    @11
    @9
    wph
    @8
    @12
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
    @12
    cK
    cn0
    wcel
    cB
    cS
    wcel
    @10
    @14
    srgpcomp.k
    srgpcomp.b
    cS
    c.ex
    cG
    cK
    cB
    @15
    srgpcomp.e
    mulgnn0cl
    syl3anc
    #
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
    wph
    @4
    @0
    cA
    @1
    c.xp
    co
    #
    c.xp
    co
    #
    @6
    wph
    @3
    @18
    @0
    c.xp
    wph
    cA
    cB
    cR
    cS
    c.xp
    c.ex
    cG
    cK
    srgpcomp.s
    srgpcomp.m
    srgpcomp.g
    srgpcomp.e
    srgpcomp.r
    srgpcomp.a
    srgpcomp.b
    srgpcomp.k
    srgpcomp.c
    srgpcomp
    oveq2d
    wph
    @8
    @9
    @11
    @10
    @6
    @19
    wceq
    srgpcomp.r
    @16
    srgpcomp.a
    @17
    cS
    cR
    c.xp
    @0
    cA
    @1
    srgpcomp.s
    srgpcomp.m
    srgass
    syl13anc
    eqtr4d
    wph
    @5
    @7
    @1
    c.xp
    wph
    @7
    @5
    wph
    @12
    @13
    @11
    @7
    @5
    wceq
    @14
    srgpcompp.n
    srgpcomp.a
    cS
    c.xp
    c.ex
    cG
    cN
    cA
    @15
    srgpcomp.e
    cR
    c.xp
    cG
    srgpcomp.g
    srgpcomp.m
    mgpplusg
    mulgnn0p1
    syl3anc
    eqcomd
    oveq1d
    3eqtrd
end
