include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "cres.mm"
include "wceq.mm"
include "cn0.mm"
include "lencl.mm"
include "wf.mm"
include "wfn.mm"
include "wa.mm"
include "wi.mm"
include "wrdf.mm"
include "ffn.mm"
include "wss.mm"
include "cz.mm"
include "nn0z.mm"
include "fzossrbm1.mm"
include "syl.mm"
include "adantr.mm"
include "adantl.mm"
include "wb.mm"
include "fnssresb.mm"
include "mpbird.mm"
include "hashfn.mm"
include "1nn0.mm"
include "nn0sub2.mm"
include "mp3an1.mm"
include "hashfzo0.mm"
include "eqtrd.mm"
include "ex.mm"
include "3syl.mm"
include "mpand.mm"
include "imp.mm"

theorem wrdred1hash
  let cS: class S
  let cF: class F


  assert |- ( ( F e. Word S /\ 1 <_ ( # ` F ) ) -> ( # ` ( F |` ( 0 ..^ ( ( # ` F ) - 1 ) ) ) ) = ( ( # ` F ) - 1 ) )

  proof
    cF
    cS
    cword
    wcel
    #
    c1
    cF
    chash
    cfv
    #
    cle
    wbr
    #
    cF
    cc0
    @1
    c1
    cmin
    co
    #
    cfzo
    co
    #
    cres
    #
    chash
    cfv
    #
    @3
    wceq
    #
    @0
    @1
    cn0
    wcel
    #
    @2
    @7
    cS
    cF
    lencl
    @0
    cc0
    @1
    cfzo
    co
    #
    cS
    cF
    wf
    cF
    @9
    wfn
    #
    @8
    @2
    wa
    #
    @7
    wi
    cS
    cF
    wrdf
    @9
    cS
    cF
    ffn
    @10
    @11
    @7
    @10
    @11
    wa
    #
    @6
    @4
    chash
    cfv
    #
    @3
    @12
    @5
    @4
    wfn
    #
    @6
    @13
    wceq
    @12
    @14
    @4
    @9
    wss
    #
    @11
    @15
    @10
    @8
    @15
    @2
    @8
    @1
    cz
    wcel
    @15
    @1
    nn0z
    @1
    fzossrbm1
    syl
    adantr
    adantl
    @10
    @14
    @15
    wb
    @11
    @9
    @4
    cF
    fnssresb
    adantr
    mpbird
    @4
    @5
    hashfn
    syl
    @11
    @13
    @3
    wceq
    #
    @10
    @11
    @3
    cn0
    wcel
    #
    @16
    c1
    cn0
    wcel
    @8
    @2
    @17
    1nn0
    c1
    @1
    nn0sub2
    mp3an1
    @3
    hashfzo0
    syl
    adantl
    eqtrd
    ex
    3syl
    mpand
    imp
end
