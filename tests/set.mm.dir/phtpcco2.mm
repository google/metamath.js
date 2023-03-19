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
include "w3a.mm"
include "isphtpc.mm"
include "sylib.mm"
include "simp1d.mm"
include "cnco.mm"
include "syl2anc.mm"
include "simp2d.mm"
include "cv.mm"
include "wex.mm"
include "simp3d.mm"
include "n0.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "phtpyco2.mm"
include "ne0i.mm"
include "syl.mm"
include "exlimddv.mm"
include "syl3anbrc.mm"

theorem phtpcco2
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vf: setvar f
  assume phtpcco2.f: |- ( ph -> F ( ~=ph ` J ) G )
  assume phtpcco2.p: |- ( ph -> P e. ( J Cn K ) )


  assert |- ( ph -> ( P o. F ) ( ~=ph ` K ) ( P o. G ) )

  proof
    wph
    cP
    cF
    ccom
    #
    cii
    cK
    ccn
    co
    #
    wcel
    #
    cP
    cG
    ccom
    #
    @1
    wcel
    #
    @0
    @3
    cK
    cphtpy
    cfv
    co
    #
    c0
    wne
    #
    @0
    @3
    cK
    cphtpc
    cfv
    wbr
    wph
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cP
    cJ
    cK
    ccn
    co
    wcel
    #
    @2
    wph
    @8
    cG
    @7
    wcel
    #
    cF
    cG
    cJ
    cphtpy
    cfv
    co
    #
    c0
    wne
    #
    wph
    cF
    cG
    cJ
    cphtpc
    cfv
    wbr
    @8
    @10
    @12
    w3a
    phtpcco2.f
    cF
    cG
    cJ
    isphtpc
    sylib
    #
    simp1d
    #
    phtpcco2.p
    cF
    cP
    cii
    cJ
    cK
    cnco
    syl2anc
    wph
    @10
    @9
    @4
    wph
    @8
    @10
    @12
    @13
    simp2d
    #
    phtpcco2.p
    cG
    cP
    cii
    cJ
    cK
    cnco
    syl2anc
    wph
    vf
    cv
    #
    @11
    wcel
    #
    @6
    vf
    wph
    @12
    @17
    vf
    wex
    wph
    @8
    @10
    @12
    @13
    simp3d
    vf
    @11
    n0
    sylib
    wph
    @17
    wa
    #
    cP
    @16
    ccom
    #
    @5
    wcel
    @6
    @18
    cP
    cF
    cG
    @16
    cJ
    cK
    wph
    @8
    @17
    @14
    adantr
    wph
    @10
    @17
    @15
    adantr
    wph
    @9
    @17
    phtpcco2.p
    adantr
    wph
    @17
    simpr
    phtpyco2
    @5
    @19
    ne0i
    syl
    exlimddv
    @0
    @3
    cK
    isphtpc
    syl3anbrc
end
