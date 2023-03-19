include "chil.mm"
include "wf.mm"
include "cei.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cel.mm"
include "csp.mm"
include "co.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cc.mm"
include "eigvalval.mm"
include "eleigveccl.mm"
include "ffvelrn.mm"
include "hicl.mm"
include "sylancom.mm"
include "syldan.mm"
include "normcl.mm"
include "recnd.mm"
include "syl.mm"
include "sqcld.mm"
include "c0v.mm"
include "wne.mm"
include "cv.mm"
include "csm.mm"
include "wceq.mm"
include "wrex.mm"
include "w3a.mm"
include "cc0.mm"
include "eleigvec.mm"
include "biimpa.mm"
include "wb.mm"
include "sqne0.mm"
include "normne0.mm"
include "bitr2d.mm"
include "3adant3.mm"
include "divcld.mm"
include "eqeltrd.mm"

theorem eigvalcl
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( T : ~H --> ~H /\ A e. ( eigvec ` T ) ) -> ( ( eigval ` T ) ` A ) e. CC )

  proof
    chil
    chil
    cT
    wf
    #
    cA
    cT
    cei
    cfv
    wcel
    #
    wa
    #
    cA
    cT
    cel
    cfv
    cfv
    cA
    cT
    cfv
    #
    cA
    csp
    co
    #
    cA
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    cc
    cA
    cT
    eigvalval
    @2
    @4
    @6
    @0
    @1
    cA
    chil
    wcel
    #
    @4
    cc
    wcel
    #
    cA
    cT
    eleigveccl
    #
    @0
    @7
    @3
    chil
    wcel
    @8
    chil
    chil
    cA
    cT
    ffvelrn
    @3
    cA
    hicl
    sylancom
    syldan
    @2
    @5
    @2
    @7
    @5
    cc
    wcel
    #
    @9
    @7
    @5
    cA
    normcl
    recnd
    #
    syl
    sqcld
    @2
    @7
    cA
    c0v
    wne
    #
    @3
    vx
    cv
    cA
    csm
    co
    wceq
    vx
    cc
    wrex
    #
    w3a
    #
    @6
    cc0
    wne
    #
    @0
    @1
    @14
    vx
    cA
    cT
    eleigvec
    biimpa
    @7
    @12
    @15
    @13
    @7
    @12
    @15
    @7
    @15
    @5
    cc0
    wne
    #
    @12
    @7
    @10
    @15
    @16
    wb
    @11
    @5
    sqne0
    syl
    cA
    normne0
    bitr2d
    biimpa
    3adant3
    syl
    divcld
    eqeltrd
end
