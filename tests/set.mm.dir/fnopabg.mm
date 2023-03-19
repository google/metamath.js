include "wmo.mm"
include "wex.mm"
include "wa.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "copab.mm"
include "wfn.mm"
include "weu.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wal.mm"
include "wi.mm"
include "moanimv.mm"
include "albii.mm"
include "funopab.mm"
include "df-ral.mm"
include "3bitr4ri.mm"
include "dmopab3.mm"
include "anbi12i.mm"
include "r19.26.mm"
include "df-fn.mm"
include "3bitr4i.mm"
include "eu5.mm"
include "ancom.mm"
include "bitri.mm"
include "ralbii.mm"
include "fneq1i.mm"

theorem fnopabg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  assume fnopabg.1: |- F = { <. x , y >. | ( x e. A /\ ph ) }

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A. x e. A E! y ph <-> F Fn A )

  proof
    wph
    vy
    wmo
    #
    wph
    vy
    wex
    #
    wa
    #
    vx
    cA
    wral
    #
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    vy
    copab
    #
    cA
    wfn
    #
    wph
    vy
    weu
    #
    vx
    cA
    wral
    cF
    cA
    wfn
    @0
    vx
    cA
    wral
    #
    @1
    vx
    cA
    wral
    #
    wa
    @6
    wfun
    #
    @6
    cdm
    cA
    wceq
    #
    wa
    @3
    @7
    @9
    @11
    @10
    @12
    @5
    vy
    wmo
    #
    vx
    wal
    @4
    @0
    wi
    #
    vx
    wal
    @11
    @9
    @13
    @14
    vx
    @4
    wph
    vy
    moanimv
    albii
    @5
    vx
    vy
    funopab
    @0
    vx
    cA
    df-ral
    3bitr4ri
    wph
    vx
    vy
    cA
    dmopab3
    anbi12i
    @0
    @1
    vx
    cA
    r19.26
    @6
    cA
    df-fn
    3bitr4i
    @8
    @2
    vx
    cA
    @8
    @1
    @0
    wa
    @2
    wph
    vy
    eu5
    @1
    @0
    ancom
    bitri
    ralbii
    cA
    cF
    @6
    fnopabg.1
    fneq1i
    3bitr4i
end
