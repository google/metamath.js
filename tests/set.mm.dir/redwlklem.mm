include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cmin.mm"
include "cfzo.mm"
include "cres.mm"
include "wa.mm"
include "wss.mm"
include "simpr.mm"
include "fzossfz.mm"
include "fssres.mm"
include "sylancl.mm"
include "ex.mm"
include "wceq.mm"
include "cz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzoval.mm"
include "syl.mm"
include "adantr.mm"
include "wb.mm"
include "wrdred1hash.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "mpbird.mm"
include "feq2d.mm"
include "sylibd.mm"
include "3impia.mm"

theorem redwlklem
  let cP: class P
  let cS: class S
  let cF: class F
  let cV: class V


  assert |- ( ( F e. Word S /\ 1 <_ ( # ` F ) /\ P : ( 0 ... ( # ` F ) ) --> V ) -> ( P |` ( 0 ..^ ( # ` F ) ) ) : ( 0 ... ( # ` ( F |` ( 0 ..^ ( ( # ` F ) - 1 ) ) ) ) ) --> V )

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
    cc0
    @1
    cfz
    co
    #
    cV
    cP
    wf
    #
    cc0
    cF
    cc0
    @1
    c1
    cmin
    co
    #
    cfzo
    co
    cres
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    cc0
    @1
    cfzo
    co
    #
    cres
    #
    wf
    #
    @0
    @2
    wa
    #
    @4
    @8
    cV
    @9
    wf
    #
    @10
    @11
    @4
    @12
    @11
    @4
    wa
    @4
    @8
    @3
    wss
    @12
    @11
    @4
    simpr
    cc0
    @1
    fzossfz
    @3
    cV
    @8
    cP
    fssres
    sylancl
    ex
    @11
    @8
    @7
    cV
    @9
    @11
    @8
    @7
    wceq
    #
    @8
    cc0
    @5
    cfz
    co
    #
    wceq
    #
    @0
    @15
    @2
    @0
    @1
    cz
    wcel
    @15
    @0
    @1
    cS
    cF
    lencl
    nn0zd
    cc0
    @1
    fzoval
    syl
    adantr
    @11
    @6
    @5
    wceq
    #
    @13
    @15
    wb
    cS
    cF
    wrdred1hash
    @16
    @7
    @14
    @8
    @6
    @5
    cc0
    cfz
    oveq2
    eqeq2d
    syl
    mpbird
    feq2d
    sylibd
    3impia
end
