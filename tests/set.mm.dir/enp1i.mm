include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "csuc.mm"
include "wne.mm"
include "nsuceq0.mm"
include "breq1.mm"
include "ensym.mm"
include "en0.mm"
include "sylib.mm"
include "syl5eqr.mm"
include "syl6bi.mm"
include "necon3ad.mm"
include "mpi.mm"
include "con2i.mm"
include "neq0.mm"
include "wi.mm"
include "breq2i.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "com.mm"
include "dif1en.mm"
include "mp3an1.mm"
include "syl.mm"
include "ex.mm"
include "sylbi.mm"
include "sylcom.mm"
include "eximdv.mm"
include "mpd.mm"

theorem enp1i
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cM: class M
  let cN: class N
  assume enp1i.1: |- M e. _om
  assume enp1i.2: |- N = suc M
  assume enp1i.3: |- ( ( A \ { x } ) ~~ M -> ph )
  assume enp1i.4: |- ( x e. A -> ( ph -> ps ) )

  disjoint A x
  disjoint N x
  assert |- ( A ~~ N -> E. x ps )

  proof
    cA
    cN
    cen
    wbr
    #
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    #
    wps
    vx
    wex
    @0
    cA
    c0
    wceq
    #
    wn
    @3
    @4
    @0
    @4
    cM
    csuc
    #
    c0
    wne
    @0
    wn
    cM
    nsuceq0
    @4
    @0
    @5
    c0
    @4
    @0
    c0
    cN
    cen
    wbr
    #
    @5
    c0
    wceq
    cA
    c0
    cN
    cen
    breq1
    @6
    @5
    cN
    c0
    enp1i.2
    @6
    cN
    c0
    cen
    wbr
    cN
    c0
    wceq
    c0
    cN
    ensym
    cN
    en0
    sylib
    syl5eqr
    syl6bi
    necon3ad
    mpi
    con2i
    vx
    cA
    neq0
    sylib
    @0
    @2
    wps
    vx
    @0
    @2
    wph
    wps
    @0
    cA
    @5
    cen
    wbr
    #
    @2
    wph
    wi
    cN
    @5
    cA
    cen
    enp1i.2
    breq2i
    @7
    @2
    wph
    @7
    @2
    wa
    cA
    @1
    csn
    cdif
    cM
    cen
    wbr
    #
    wph
    cM
    com
    wcel
    @7
    @2
    @8
    enp1i.1
    cA
    cM
    @1
    dif1en
    mp3an1
    enp1i.3
    syl
    ex
    sylbi
    enp1i.4
    sylcom
    eximdv
    mpd
end
