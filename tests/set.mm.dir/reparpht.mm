include "ccom.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cphtpy.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cphtpc.mm"
include "wbr.mm"
include "cnco.mm"
include "syl2anc.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cv.mm"
include "cmin.mm"
include "cmul.mm"
include "caddc.mm"
include "cmpt2.mm"
include "eqid.mm"
include "reparphti.mm"
include "ne0i.mm"
include "syl.mm"
include "isphtpc.mm"
include "syl3anbrc.mm"

theorem reparpht
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cJ: class J
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cH: class H
  let vz: setvar z
  assume reparpht.2: |- ( ph -> F e. ( II Cn J ) )
  assume reparpht.3: |- ( ph -> G e. ( II Cn II ) )
  assume reparpht.4: |- ( ph -> ( G ` 0 ) = 0 )
  assume reparpht.5: |- ( ph -> ( G ` 1 ) = 1 )


  assert |- ( ph -> ( F o. G ) ( ~=ph ` J ) F )

  proof
    wph
    cF
    cG
    ccom
    #
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cF
    @1
    wcel
    #
    @0
    cF
    cJ
    cphtpy
    cfv
    co
    #
    c0
    wne
    #
    @0
    cF
    cJ
    cphtpc
    cfv
    wbr
    wph
    cG
    cii
    cii
    ccn
    co
    wcel
    @3
    @2
    reparpht.3
    reparpht.2
    cG
    cF
    cii
    cii
    cJ
    cnco
    syl2anc
    reparpht.2
    wph
    vx
    vy
    cc0
    c1
    cicc
    co
    #
    @6
    c1
    vy
    cv
    #
    cmin
    co
    vx
    cv
    #
    cG
    cfv
    cmul
    co
    @7
    @8
    cmul
    co
    caddc
    co
    cF
    cfv
    cmpt2
    #
    @4
    wcel
    @5
    wph
    vx
    vy
    cF
    cG
    @9
    cJ
    reparpht.2
    reparpht.3
    reparpht.4
    reparpht.5
    @9
    eqid
    reparphti
    @4
    @9
    ne0i
    syl
    @0
    cF
    cJ
    isphtpc
    syl3anbrc
end
