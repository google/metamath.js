include "wss.mm"
include "cr.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "ovolss.mm"
include "3adant3.mm"
include "simp3.mm"
include "breqtrd.mm"
include "sstr.mm"
include "ovolge0.mm"
include "syl.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "ovolcl.mm"
include "0xr.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem ovolssnul
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let wph: wff ph
  let cS: class S
  let cT: class T


  assert |- ( ( A C_ B /\ B C_ RR /\ ( vol* ` B ) = 0 ) -> ( vol* ` A ) = 0 )

  proof
    cA
    cB
    wss
    #
    cB
    cr
    wss
    #
    cB
    covol
    cfv
    #
    cc0
    wceq
    #
    w3a
    #
    cA
    covol
    cfv
    #
    cc0
    wceq
    #
    @5
    cc0
    cle
    wbr
    #
    cc0
    @5
    cle
    wbr
    #
    @4
    @5
    @2
    cc0
    cle
    @0
    @1
    @5
    @2
    cle
    wbr
    @3
    cA
    cB
    ovolss
    3adant3
    @0
    @1
    @3
    simp3
    breqtrd
    @4
    cA
    cr
    wss
    #
    @8
    @0
    @1
    @9
    @3
    cA
    cB
    cr
    sstr
    3adant3
    #
    cA
    ovolge0
    syl
    @4
    @5
    cxr
    wcel
    #
    cc0
    cxr
    wcel
    @6
    @7
    @8
    wa
    wb
    @4
    @9
    @11
    @10
    cA
    ovolcl
    syl
    0xr
    @5
    cc0
    xrletri3
    sylancl
    mpbir2and
end
