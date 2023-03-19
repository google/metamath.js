include "ccnv.mm"
include "wfun.mm"
include "cdm.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "cop.mm"
include "structfun.mm"
include "cn.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cstr.mm"
include "isstruct.mm"
include "mpbi.mm"
include "simp3i.mm"
include "cuz.mm"
include "cfv.mm"
include "simp1i.mm"
include "elnnuz.mm"
include "fzss1.mm"
include "ax-mp.mm"
include "sstri.mm"
include "pm3.2i.mm"

theorem structfn
  let cF: class F
  let cM: class M
  let cN: class N
  assume structfn.1: |- F Struct <. M , N >.


  assert |- ( Fun `' `' F /\ dom F C_ ( 1 ... N ) )

  proof
    cF
    ccnv
    ccnv
    wfun
    cF
    cdm
    #
    c1
    cN
    cfz
    co
    #
    wss
    cF
    cM
    cN
    cop
    #
    structfn.1
    structfun
    @0
    cM
    cN
    cfz
    co
    #
    @1
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    cF
    c0
    csn
    cdif
    wfun
    #
    @0
    @3
    wss
    #
    cF
    @2
    cstr
    wbr
    @7
    @8
    @9
    w3a
    structfn.1
    cF
    cM
    cN
    isstruct
    mpbi
    #
    simp3i
    cM
    c1
    cuz
    cfv
    wcel
    #
    @3
    @1
    wss
    @4
    @11
    @4
    @5
    @6
    @7
    @8
    @9
    @10
    simp1i
    simp1i
    cM
    elnnuz
    mpbi
    cM
    c1
    cN
    fzss1
    ax-mp
    sstri
    pm3.2i
end
