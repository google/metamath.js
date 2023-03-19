include "cop.mm"
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
include "w3a.mm"
include "co.mm"
include "isstruct2.mm"
include "brinxp2.mm"
include "df-br.mm"
include "bitr3i.mm"
include "biid.mm"
include "df-ov.mm"
include "sseq2i.mm"
include "3anbi123i.mm"
include "bitr4i.mm"

theorem isstruct
  let cF: class F
  let cM: class M
  let cN: class N


  assert |- ( F Struct <. M , N >. <-> ( ( M e. NN /\ N e. NN /\ M <_ N ) /\ Fun ( F \ { (/) } ) /\ dom F C_ ( M ... N ) ) )

  proof
    cF
    cM
    cN
    cop
    #
    cstr
    wbr
    @0
    cle
    cn
    cn
    cxp
    cin
    #
    wcel
    #
    cF
    c0
    csn
    cdif
    wfun
    #
    cF
    cdm
    #
    @0
    cfz
    cfv
    #
    wss
    #
    w3a
    cM
    cn
    wcel
    cN
    cn
    wcel
    cM
    cN
    cle
    wbr
    w3a
    #
    @3
    @4
    cM
    cN
    cfz
    co
    #
    wss
    #
    w3a
    cF
    @0
    isstruct2
    @7
    @2
    @3
    @3
    @9
    @6
    @7
    cM
    cN
    @1
    wbr
    @2
    cM
    cN
    cn
    cn
    cle
    brinxp2
    cM
    cN
    @1
    df-br
    bitr3i
    @3
    biid
    @8
    @5
    @4
    cM
    cN
    cfz
    df-ov
    sseq2i
    3anbi123i
    bitr4i
end
