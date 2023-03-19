include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "cminusg.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "lmodvsubval2.mm"
include "syl3anc.mm"
include "coppr.mm"
include "lcdsca.mm"
include "fveq2d.mm"
include "opprneg.mm"
include "syl6reqr.mm"
include "oppr1.mm"
include "fveq12d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem lcdvsub
  let wph: wff ph
  let cC: class C
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  assume lcdvsub.h: |- H = ( LHyp ` K )
  assume lcdvsub.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvsub.s: |- S = ( Scalar ` U )
  assume lcdvsub.n: |- N = ( invg ` S )
  assume lcdvsub.e: |- .1. = ( 1r ` S )
  assume lcdvsub.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvsub.v: |- V = ( Base ` C )
  assume lcdvsub.p: |- .+ = ( +g ` C )
  assume lcdvsub.t: |- .x. = ( .s ` C )
  assume lcdvsub.m: |- .- = ( -g ` C )
  assume lcdvsub.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdvsub.f: |- ( ph -> F e. V )
  assume lcdvsub.g: |- ( ph -> G e. V )


  assert |- ( ph -> ( F .- G ) = ( F .+ ( ( N ` .1. ) .x. G ) ) )

  proof
    wph
    cF
    cG
    c.mi
    co
    #
    cF
    cC
    csca
    cfv
    #
    cur
    cfv
    #
    @1
    cminusg
    cfv
    #
    cfv
    #
    cG
    c.x
    co
    #
    c.pl
    co
    #
    cF
    c.1
    cN
    cfv
    #
    cG
    c.x
    co
    #
    c.pl
    co
    wph
    cC
    clmod
    wcel
    cF
    cV
    wcel
    cG
    cV
    wcel
    @0
    @6
    wceq
    wph
    cC
    cH
    cK
    cW
    lcdvsub.h
    lcdvsub.c
    lcdvsub.k
    lcdlmod
    lcdvsub.f
    lcdvsub.g
    cF
    cG
    c.pl
    c.x
    @2
    @1
    c.mi
    @3
    cV
    cC
    lcdvsub.v
    lcdvsub.p
    lcdvsub.m
    @1
    eqid
    #
    lcdvsub.t
    @3
    eqid
    @2
    eqid
    lmodvsubval2
    syl3anc
    wph
    @8
    @5
    cF
    c.pl
    wph
    @7
    @4
    cG
    c.x
    wph
    c.1
    @2
    cN
    @3
    wph
    @3
    cS
    coppr
    cfv
    #
    cminusg
    cfv
    cN
    wph
    @1
    @10
    cminusg
    wph
    cC
    @1
    cU
    cS
    cH
    cK
    @10
    cW
    lcdvsub.h
    lcdvsub.u
    lcdvsub.s
    @10
    eqid
    #
    lcdvsub.c
    @9
    lcdvsub.k
    lcdsca
    #
    fveq2d
    cS
    cN
    @10
    @11
    lcdvsub.n
    opprneg
    syl6reqr
    wph
    @2
    @10
    cur
    cfv
    c.1
    wph
    @1
    @10
    cur
    @12
    fveq2d
    cS
    c.1
    @10
    @11
    lcdvsub.e
    oppr1
    syl6reqr
    fveq12d
    oveq1d
    oveq2d
    eqtr4d
end
