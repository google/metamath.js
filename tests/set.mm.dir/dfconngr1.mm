include "cconngr.mm"
include "cv.mm"
include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "wral.mm"
include "cvtx.mm"
include "wsbc.mm"
include "cab.mm"
include "csn.mm"
include "cdif.mm"
include "df-conngr.mm"
include "wb.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "raleqdv.mm"
include "ralunb.mm"
include "syl6bb.mm"
include "eqid.mm"
include "0pthonv.mm"
include "wceq.mm"
include "oveq2.mm"
include "breqd.mm"
include "2exbidv.mm"
include "ralsng.mm"
include "mpbird.mm"
include "biantrud.mm"
include "bitr4d.mm"
include "ralbiia.mm"
include "fvex.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "difeq1.mm"
include "bibi12d.mm"
include "sbcie.mm"
include "mpbir.mm"
include "sbcbi1.mm"
include "ax-mp.mm"
include "abbii.mm"
include "eqtri.mm"

theorem dfconngr1
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p

  disjoint g v
  disjoint g k
  disjoint g n
  disjoint f g
  disjoint g p
  disjoint k v
  disjoint n v
  disjoint f v
  disjoint p v
  disjoint k n
  disjoint f k
  disjoint k p
  disjoint f n
  disjoint n p
  disjoint f p
  assert |- ConnGraph = { g | [. ( Vtx ` g ) / v ]. A. k e. v A. n e. ( v \ { k } ) E. f E. p f ( k ( PathsOn ` g ) n ) p }

  proof
    cconngr
    vf
    cv
    #
    vp
    cv
    #
    vk
    cv
    #
    vn
    cv
    #
    vg
    cv
    #
    cpthson
    cfv
    #
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    vn
    vv
    cv
    #
    wral
    #
    vk
    @9
    wral
    #
    vv
    @4
    cvtx
    cfv
    #
    wsbc
    #
    vg
    cab
    @8
    vn
    @9
    @2
    csn
    #
    cdif
    #
    wral
    #
    vk
    @9
    wral
    #
    vv
    @12
    wsbc
    #
    vg
    cab
    vv
    vf
    vg
    vk
    vn
    vp
    df-conngr
    @13
    @18
    vg
    @11
    @17
    wb
    #
    vv
    @12
    wsbc
    #
    @13
    @18
    wb
    @20
    @8
    vn
    @12
    wral
    #
    vk
    @12
    wral
    #
    @8
    vn
    @12
    @14
    cdif
    #
    wral
    #
    vk
    @12
    wral
    #
    wb
    #
    @21
    @24
    vk
    @12
    @2
    @12
    wcel
    #
    @21
    @24
    @8
    vn
    @14
    wral
    #
    wa
    #
    @24
    @27
    @21
    @8
    vn
    @23
    @14
    cun
    #
    wral
    @29
    @27
    @8
    vn
    @12
    @30
    @27
    @30
    @12
    @12
    @2
    difsnid
    eqcomd
    raleqdv
    @8
    vn
    @23
    @14
    ralunb
    syl6bb
    @27
    @28
    @24
    @27
    @28
    @0
    @1
    @2
    @2
    @5
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    vf
    @4
    @2
    @12
    vp
    @12
    eqid
    0pthonv
    @8
    @33
    vn
    @2
    @12
    @3
    @2
    wceq
    #
    @7
    @32
    vf
    vp
    @34
    @6
    @31
    @0
    @1
    @3
    @2
    @2
    @5
    oveq2
    breqd
    2exbidv
    ralsng
    mpbird
    biantrud
    bitr4d
    ralbiia
    @19
    @26
    vv
    @12
    @4
    cvtx
    fvex
    @9
    @12
    wceq
    #
    @11
    @22
    @17
    @25
    @10
    @21
    vk
    @9
    @12
    @8
    vn
    @9
    @12
    raleq
    raleqbi1dv
    @16
    @24
    vk
    @9
    @12
    @35
    @8
    vn
    @15
    @23
    @9
    @12
    @14
    difeq1
    raleqdv
    raleqbi1dv
    bibi12d
    sbcie
    mpbir
    @11
    @17
    vv
    @12
    sbcbi1
    ax-mp
    abbii
    eqtri
end
