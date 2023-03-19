include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "co.mm"
include "cmgm.mm"
include "wi.mm"
include "eqid.mm"
include "mgmcl.mm"
include "3expib.mm"
include "syl.mm"
include "imp.mm"
include "gsumpropd2.mm"

theorem gsummgmpropd
  let wph: wff ph
  let vt: setvar t
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  assume gsummgmpropd.f: |- ( ph -> F e. V )
  assume gsummgmpropd.g: |- ( ph -> G e. W )
  assume gsummgmpropd.h: |- ( ph -> H e. X )
  assume gsummgmpropd.b: |- ( ph -> ( Base ` G ) = ( Base ` H ) )
  assume gsummgmpropd.m: |- ( ph -> G e. Mgm )
  assume gsummgmpropd.e: |- ( ( ph /\ ( s e. ( Base ` G ) /\ t e. ( Base ` G ) ) ) -> ( s ( +g ` G ) t ) = ( s ( +g ` H ) t ) )
  assume gsummgmpropd.n: |- ( ph -> Fun F )
  assume gsummgmpropd.r: |- ( ph -> ran F C_ ( Base ` G ) )

  disjoint F s
  disjoint F t
  disjoint s t
  disjoint G s
  disjoint G t
  disjoint H s
  disjoint H t
  disjoint ph s
  disjoint ph t
  assert |- ( ph -> ( G gsum F ) = ( H gsum F ) )

  proof
    wph
    vt
    cF
    cG
    cH
    cV
    cW
    cX
    vs
    gsummgmpropd.f
    gsummgmpropd.g
    gsummgmpropd.h
    gsummgmpropd.b
    wph
    vs
    cv
    #
    cG
    cbs
    cfv
    #
    wcel
    #
    vt
    cv
    #
    @1
    wcel
    #
    wa
    #
    @0
    @3
    cG
    cplusg
    cfv
    #
    co
    @1
    wcel
    #
    wph
    cG
    cmgm
    wcel
    #
    @5
    @7
    wi
    gsummgmpropd.m
    @8
    @2
    @4
    @7
    @1
    cG
    @0
    @3
    @6
    @1
    eqid
    @6
    eqid
    mgmcl
    3expib
    syl
    imp
    gsummgmpropd.e
    gsummgmpropd.n
    gsummgmpropd.r
    gsumpropd2
end
