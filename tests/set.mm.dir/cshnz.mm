include "cz.mm"
include "wcel.mm"
include "wn.mm"
include "ccsh.mm"
include "cdm.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wfn.mm"
include "cn0.mm"
include "wrex.mm"
include "cab.mm"
include "cxp.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "chash.mm"
include "cfv.mm"
include "cmo.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "cif.mm"
include "df-csh.mm"
include "0ex.mm"
include "ovex.mm"
include "ifex.mm"
include "dmmpt2.mm"
include "id.mm"
include "intnand.mm"
include "ndmovg.mm"
include "sylancr.mm"

theorem cshnz
  let cN: class N
  let cW: class W
  let vf: setvar f
  let vl: setvar l
  let vn: setvar n
  let vw: setvar w


  assert |- ( -. N e. ZZ -> ( W cyclShift N ) = (/) )

  proof
    cN
    cz
    wcel
    #
    wn
    #
    ccsh
    cdm
    vf
    cv
    cc0
    vl
    cv
    cfzo
    co
    wfn
    vl
    cn0
    wrex
    vf
    cab
    #
    cz
    cxp
    wceq
    cW
    @2
    wcel
    #
    @0
    wa
    wn
    cW
    cN
    ccsh
    co
    c0
    wceq
    vw
    vn
    @2
    cz
    vw
    cv
    #
    c0
    wceq
    #
    c0
    @4
    vn
    cv
    @4
    chash
    cfv
    #
    cmo
    co
    #
    @6
    cop
    csubstr
    co
    #
    @4
    cc0
    @7
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    cif
    ccsh
    vw
    vf
    vn
    vl
    df-csh
    @5
    c0
    @10
    0ex
    @8
    @9
    cconcat
    ovex
    ifex
    dmmpt2
    @1
    @0
    @3
    @1
    id
    intnand
    cW
    cN
    @2
    cz
    ccsh
    ndmovg
    sylancr
end
