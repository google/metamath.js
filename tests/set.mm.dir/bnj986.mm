include "cv.mm"
include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wfn.mm"
include "wrex.mm"
include "bnj158.mm"
include "bnj769.mm"
include "bnj1196.mm"
include "vex.mm"
include "sucex.mm"
include "isseti.mm"
include "jctir.mm"
include "exdistr.mm"
include "19.41v.mm"
include "bitr2i.mm"
include "sylib.mm"
include "w3a.mm"
include "df-3an.mm"
include "bitri.mm"
include "2exbii.mm"
include "sylibr.mm"

theorem bnj986
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let cD: class D
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  assume bnj986.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj986.10: |- D = ( _om \ { (/) } )
  assume bnj986.15: |- ( ta <-> ( m e. _om /\ n = suc m /\ p = suc n ) )

  disjoint m n
  disjoint m p
  disjoint n p
  assert |- ( ch -> E. m E. p ta )

  proof
    wch
    vm
    cv
    #
    com
    wcel
    #
    vn
    cv
    #
    @0
    csuc
    wceq
    #
    wa
    #
    vp
    cv
    @2
    csuc
    #
    wceq
    #
    wa
    #
    vp
    wex
    vm
    wex
    #
    wta
    vp
    wex
    vm
    wex
    wch
    @4
    vm
    wex
    #
    @6
    vp
    wex
    #
    wa
    #
    @8
    wch
    @9
    @10
    wch
    @3
    vm
    com
    @2
    cD
    wcel
    vf
    cv
    @2
    wfn
    wph
    wps
    @3
    vm
    com
    wrex
    wch
    bnj986.3
    cD
    vn
    vm
    bnj986.10
    bnj158
    bnj769
    bnj1196
    vp
    @5
    @2
    vn
    vex
    sucex
    isseti
    jctir
    @8
    @4
    @10
    wa
    vm
    wex
    @11
    @4
    @6
    vm
    vp
    exdistr
    @4
    @10
    vm
    19.41v
    bitr2i
    sylib
    wta
    @7
    vm
    vp
    wta
    @1
    @3
    @6
    w3a
    @7
    bnj986.15
    @1
    @3
    @6
    df-3an
    bitri
    2exbii
    sylibr
end
