include "cmul.mm"
include "cv.mm"
include "co.mm"
include "remulcl.mm"
include "mulcl.mm"
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
include "absmuld.mm"
include "abscld.mm"
include "simp1l.mm"
include "simp1r.mm"
include "absge0d.mm"
include "simp3l.mm"
include "simp3r.mm"
include "lemul12ad.mm"
include "eqbrtrd.mm"
include "3expia.mm"
include "o1of2.mm"

theorem o1mul
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


  assert |- ( ( F e. O(1) /\ G e. O(1) ) -> ( F oF x. G ) e. O(1) )

  proof
    vx
    vy
    cmul
    vm
    vn
    cF
    cG
    vm
    cv
    #
    vn
    cv
    #
    cmul
    co
    #
    @0
    @1
    remulcl
    vx
    cv
    #
    vy
    cv
    #
    mulcl
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
    cmul
    co
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
    @16
    @11
    @13
    cmul
    co
    @2
    cle
    @17
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
    absmuld
    @17
    @11
    @0
    @13
    @1
    @17
    @3
    @18
    abscld
    @5
    @6
    @10
    @15
    simp1l
    @17
    @4
    @19
    abscld
    @5
    @6
    @10
    @15
    simp1r
    @17
    @3
    @18
    absge0d
    @17
    @4
    @19
    absge0d
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
    lemul12ad
    eqbrtrd
    3expia
    o1of2
end
