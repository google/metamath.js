include "cphtpy.mm"
include "cfv.mm"
include "co.mm"
include "cii.mm"
include "chtpy.mm"
include "ctx.mm"
include "ccn.mm"
include "phtpyhtpy.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "ctopon.mm"
include "wcel.mm"
include "iitopon.mm"
include "a1i.mm"
include "htpycn.mm"
include "sstrd.mm"

theorem phtpycn
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cJ: class J
  let cA: class A
  let vs: setvar s
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cH: class H
  let cK: class K
  let vj: setvar j
  assume isphtpy.2: |- ( ph -> F e. ( II Cn J ) )
  assume isphtpy.3: |- ( ph -> G e. ( II Cn J ) )


  assert |- ( ph -> ( F ( PHtpy ` J ) G ) C_ ( ( II tX II ) Cn J ) )

  proof
    wph
    cF
    cG
    cJ
    cphtpy
    cfv
    co
    cF
    cG
    cii
    cJ
    chtpy
    co
    co
    cii
    cii
    ctx
    co
    cJ
    ccn
    co
    wph
    cF
    cG
    cJ
    isphtpy.2
    isphtpy.3
    phtpyhtpy
    wph
    cF
    cG
    cii
    cJ
    cc0
    c1
    cicc
    co
    #
    cii
    @0
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    isphtpy.2
    isphtpy.3
    htpycn
    sstrd
end
