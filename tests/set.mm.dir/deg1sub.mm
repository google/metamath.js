include "co.mm"
include "cfv.mm"
include "cminusg.mm"
include "cplusg.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "cgrp.mm"
include "crg.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "3syl.mm"
include "grpinvcl.mm"
include "clt.mm"
include "deg1invg.mm"
include "eqbrtrd.mm"
include "deg1add.mm"
include "eqtrd.mm"

theorem deg1sub
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cY: class Y
  assume deg1addle.y: |- Y = ( Poly1 ` R )
  assume deg1addle.d: |- D = ( deg1 ` R )
  assume deg1addle.r: |- ( ph -> R e. Ring )
  assume deg1suble.b: |- B = ( Base ` Y )
  assume deg1suble.m: |- .- = ( -g ` Y )
  assume deg1suble.f: |- ( ph -> F e. B )
  assume deg1suble.g: |- ( ph -> G e. B )
  assume deg1sub.l: |- ( ph -> ( D ` G ) < ( D ` F ) )


  assert |- ( ph -> ( D ` ( F .- G ) ) = ( D ` F ) )

  proof
    wph
    cF
    cG
    c.mi
    co
    #
    cD
    cfv
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
    cD
    cfv
    cF
    cD
    cfv
    #
    wph
    @0
    @4
    cD
    wph
    cF
    cB
    wcel
    cG
    cB
    wcel
    #
    @0
    @4
    wceq
    deg1suble.f
    deg1suble.g
    cB
    @3
    cY
    @1
    c.mi
    cF
    cG
    deg1suble.b
    @3
    eqid
    #
    @1
    eqid
    #
    deg1suble.m
    grpsubval
    syl2anc
    fveq2d
    wph
    cB
    cD
    @3
    cR
    cF
    @2
    cY
    deg1addle.y
    deg1addle.d
    deg1addle.r
    deg1suble.b
    @7
    deg1suble.f
    wph
    cY
    cgrp
    wcel
    #
    @6
    @2
    cB
    wcel
    wph
    cR
    crg
    wcel
    cY
    crg
    wcel
    @9
    deg1addle.r
    cY
    cR
    deg1addle.y
    ply1ring
    cY
    ringgrp
    3syl
    deg1suble.g
    cB
    cY
    @1
    cG
    deg1suble.b
    @8
    grpinvcl
    syl2anc
    wph
    @2
    cD
    cfv
    cG
    cD
    cfv
    @5
    clt
    wph
    cB
    cD
    cR
    cG
    @1
    cY
    deg1addle.y
    deg1addle.d
    deg1addle.r
    deg1suble.b
    @8
    deg1suble.g
    deg1invg
    deg1sub.l
    eqbrtrd
    deg1add
    eqtrd
end
