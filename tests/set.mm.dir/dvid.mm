include "cc.mm"
include "cid.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "c1.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "wtru.mm"
include "wf1o.mm"
include "wf.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "cv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "simp2.mm"
include "simp1.mm"
include "subcld.mm"
include "simp3.mm"
include "subne0d.mm"
include "fvresi.mm"
include "oveqan12rd.mm"
include "3adant3.mm"
include "diveq1bd.mm"
include "adantl.mm"
include "ax-1cn.mm"
include "dvidlem.mm"
include "trud.mm"

theorem dvid
  let vx: setvar x
  let vz: setvar z
  let cA: class A


  assert |- ( CC _D ( _I |` CC ) ) = ( CC X. { 1 } )

  proof
    cc
    cid
    cc
    cres
    #
    cdv
    co
    cc
    c1
    csn
    cxp
    wceq
    wtru
    vx
    vz
    c1
    @0
    cc
    cc
    @0
    wf1o
    cc
    cc
    @0
    wf
    wtru
    cc
    f1oi
    cc
    cc
    @0
    f1of
    mp1i
    vx
    cv
    #
    cc
    wcel
    #
    vz
    cv
    #
    cc
    wcel
    #
    @3
    @1
    wne
    #
    w3a
    #
    @3
    @0
    cfv
    #
    @1
    @0
    cfv
    #
    cmin
    co
    #
    @3
    @1
    cmin
    co
    #
    cdiv
    co
    c1
    wceq
    wtru
    @6
    @9
    @10
    @6
    @3
    @1
    @2
    @4
    @5
    simp2
    #
    @2
    @4
    @5
    simp1
    #
    subcld
    @6
    @3
    @1
    @11
    @12
    @2
    @4
    @5
    simp3
    subne0d
    @2
    @4
    @9
    @10
    wceq
    @5
    @4
    @2
    @7
    @3
    @8
    @1
    cmin
    cc
    @3
    fvresi
    cc
    @1
    fvresi
    oveqan12rd
    3adant3
    diveq1bd
    adantl
    ax-1cn
    dvidlem
    trud
end
