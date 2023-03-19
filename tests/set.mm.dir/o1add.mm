include "caddc.mm"
include "cv.mm"
include "co.mm"
include "readdcl.mm"
include "addcl.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "simp2l.mm"
include "simp2r.mm"
include "addcld.mm"
include "abscld.mm"
include "readdcld.mm"
include "simp1l.mm"
include "simp1r.mm"
include "abstrid.mm"
include "simp3l.mm"
include "simp3r.mm"
include "le2addd.mm"
include "letrd.mm"
include "3expia.mm"
include "o1of2.mm"

theorem o1add
  let cF: class F
  let cG: class G
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n


  assert |- ( ( F e. O(1) /\ G e. O(1) ) -> ( F oF + G ) e. O(1) )

  proof
    vm
    vn
    caddc
    vx
    vy
    cF
    cG
    vx
    cv
    #
    vy
    cv
    #
    caddc
    co
    #
    @0
    @1
    readdcl
    vm
    cv
    #
    vn
    cv
    #
    addcl
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    #
    @3
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    wa
    #
    @3
    cabs
    cfv
    #
    @0
    cle
    wbr
    #
    @4
    cabs
    cfv
    #
    @1
    cle
    wbr
    #
    wa
    #
    @3
    @4
    caddc
    co
    #
    cabs
    cfv
    #
    @2
    cle
    wbr
    @7
    @10
    @15
    w3a
    #
    @17
    @11
    @13
    caddc
    co
    @2
    @18
    @16
    @18
    @3
    @4
    @7
    @8
    @9
    @15
    simp2l
    #
    @7
    @8
    @9
    @15
    simp2r
    #
    addcld
    abscld
    @18
    @11
    @13
    @18
    @3
    @19
    abscld
    #
    @18
    @4
    @20
    abscld
    #
    readdcld
    @18
    @0
    @1
    @5
    @6
    @10
    @15
    simp1l
    #
    @5
    @6
    @10
    @15
    simp1r
    #
    readdcld
    @18
    @3
    @4
    @19
    @20
    abstrid
    @18
    @11
    @13
    @0
    @1
    @21
    @22
    @23
    @24
    @7
    @10
    @12
    @14
    simp3l
    @7
    @10
    @12
    @14
    simp3r
    le2addd
    letrd
    3expia
    o1of2
end
