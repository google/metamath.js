include "cstr.mm"
include "wbr.mm"
include "cle.mm"
include "cn.mm"
include "cxp.mm"
include "cin.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cdm.mm"
include "cfz.mm"
include "cfv.mm"
include "wss.mm"
include "isstruct2.mm"
include "simp2bi.mm"

theorem structn0fun
  let cF: class F
  let cX: class X


  assert |- ( F Struct X -> Fun ( F \ { (/) } ) )

  proof
    cF
    cX
    cstr
    wbr
    cX
    cle
    cn
    cn
    cxp
    cin
    wcel
    cF
    c0
    csn
    cdif
    wfun
    cF
    cdm
    cX
    cfz
    cfv
    wss
    cF
    cX
    isstruct2
    simp2bi
end
