include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cpthson.mm"
include "wbr.mm"
include "ctrlson.mm"
include "cpths.mm"
include "0trlon.mm"
include "simpl.mm"
include "wcel.mm"
include "cvv.mm"
include "wb.mm"
include "id.mm"
include "cz.mm"
include "0z.mm"
include "elfz3.mm"
include "mp1i.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbid.mm"
include "1vgrex.mm"
include "0pth.mm"
include "3syl.mm"
include "mpbird.mm"
include "cpm.mm"
include "0wlkonlem1.mm"
include "0wlkonlem2.mm"
include "0ex.mm"
include "jctil.mm"
include "ispthson.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem 0pthon
  let cP: class P
  let cG: class G
  let cN: class N
  let cV: class V
  assume 0pthon.v: |- V = ( Vtx ` G )


  assert |- ( ( P : ( 0 ... 0 ) --> V /\ ( P ` 0 ) = N ) -> (/) ( N ( PathsOn ` G ) N ) P )

  proof
    cc0
    cc0
    cfz
    co
    #
    cV
    cP
    wf
    #
    cc0
    cP
    cfv
    #
    cN
    wceq
    #
    wa
    #
    c0
    cP
    cN
    cN
    cG
    cpthson
    cfv
    co
    wbr
    #
    c0
    cP
    cN
    cN
    cG
    ctrlson
    cfv
    co
    wbr
    #
    c0
    cP
    cG
    cpths
    cfv
    wbr
    #
    cP
    cG
    cN
    cV
    0pthon.v
    0trlon
    @4
    @7
    @1
    @1
    @3
    simpl
    @4
    cN
    cV
    wcel
    #
    cG
    cvv
    wcel
    @7
    @1
    wb
    @4
    @2
    cV
    wcel
    #
    @8
    @1
    @9
    @3
    @1
    @0
    cV
    cc0
    cP
    @1
    id
    cc0
    cz
    wcel
    cc0
    @0
    wcel
    @1
    0z
    cc0
    elfz3
    mp1i
    ffvelrnd
    adantr
    @3
    @9
    @8
    wb
    @1
    @2
    cN
    cV
    eleq1
    adantl
    mpbid
    cG
    cN
    cV
    0pthon.v
    1vgrex
    cP
    cG
    cV
    cvv
    0pthon.v
    0pth
    3syl
    mpbird
    @4
    @8
    @8
    wa
    c0
    cvv
    wcel
    #
    cP
    cV
    @0
    cpm
    co
    #
    wcel
    #
    wa
    @5
    @6
    @7
    wa
    wb
    cP
    cG
    cN
    cV
    0pthon.v
    0wlkonlem1
    @4
    @12
    @10
    cP
    cG
    cN
    cV
    0pthon.v
    0wlkonlem2
    0ex
    jctil
    cN
    cN
    cP
    cvv
    c0
    cG
    cV
    @11
    0pthon.v
    ispthson
    syl2anc
    mpbir2and
end
