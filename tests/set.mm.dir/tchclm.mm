include "clmod.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cbs.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "cclm.mm"
include "cphl.mm"
include "phllmod.mm"
include "syl.mm"
include "cc.mm"
include "cin.mm"
include "eqid.mm"
include "clvec.mm"
include "cdr.mm"
include "phllvec.mm"
include "lvecdrng.mm"
include "cphsubrglem.mm"
include "simp1d.mm"
include "simp3d.mm"
include "isclm.mm"
include "syl3anbrc.mm"

theorem tchclm
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let c.mi: class .-
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let c.xi: class .,
  let cC: class C
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchcph.v: |- V = ( Base ` W )
  assume tchcph.f: |- F = ( Scalar ` W )
  assume tchcph.1: |- ( ph -> W e. PreHil )
  assume tchcph.2: |- ( ph -> F = ( CCfld |`s K ) )


  assert |- ( ph -> W e. CMod )

  proof
    wph
    cW
    clmod
    wcel
    #
    cF
    ccnfld
    cF
    cbs
    cfv
    #
    cress
    co
    wceq
    #
    @1
    ccnfld
    csubrg
    cfv
    wcel
    #
    cW
    cclm
    wcel
    wph
    cW
    cphl
    wcel
    #
    @0
    tchcph.1
    cW
    phllmod
    syl
    wph
    @2
    @1
    cK
    cc
    cin
    wceq
    #
    @3
    wph
    cK
    cF
    @1
    @1
    eqid
    #
    tchcph.2
    wph
    cW
    clvec
    wcel
    #
    cF
    cdr
    wcel
    wph
    @4
    @7
    tchcph.1
    cW
    phllvec
    syl
    cF
    cW
    tchcph.f
    lvecdrng
    syl
    cphsubrglem
    #
    simp1d
    wph
    @2
    @5
    @3
    @8
    simp3d
    cF
    @1
    cW
    tchcph.f
    @6
    isclm
    syl3anbrc
end
