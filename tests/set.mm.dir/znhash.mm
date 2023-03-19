include "cn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "czrh.mm"
include "wceq.mm"
include "cz.mm"
include "cif.mm"
include "cres.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "cn0.mm"
include "nnnn0.mm"
include "eqid.mm"
include "znf1o.mm"
include "syl.mm"
include "wne.mm"
include "wb.mm"
include "nnne0.mm"
include "ifnefalse.mm"
include "f1oeq2.mm"
include "3syl.mm"
include "mpbid.mm"
include "ovex.mm"
include "f1oen.mm"
include "ensym.mm"
include "hasheni.mm"
include "4syl.mm"
include "hashfzo0.mm"
include "eqtrd.mm"

theorem znhash
  let cB: class B
  let cN: class N
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume zntos.y: |- Y = ( Z/nZ ` N )
  assume znhash.1: |- B = ( Base ` Y )


  assert |- ( N e. NN -> ( # ` B ) = N )

  proof
    cN
    cn
    wcel
    #
    cB
    chash
    cfv
    #
    cc0
    cN
    cfzo
    co
    #
    chash
    cfv
    #
    cN
    @0
    @2
    cB
    cY
    czrh
    cfv
    cN
    cc0
    wceq
    cz
    @2
    cif
    #
    cres
    #
    wf1o
    #
    @2
    cB
    cen
    wbr
    cB
    @2
    cen
    wbr
    @1
    @3
    wceq
    @0
    @4
    cB
    @5
    wf1o
    #
    @6
    @0
    cN
    cn0
    wcel
    #
    @7
    cN
    nnnn0
    #
    cB
    @5
    cN
    @4
    cY
    zntos.y
    znhash.1
    @5
    eqid
    @4
    eqid
    znf1o
    syl
    @0
    cN
    cc0
    wne
    @4
    @2
    wceq
    @7
    @6
    wb
    cN
    nnne0
    cN
    cc0
    cz
    @2
    ifnefalse
    @4
    @2
    cB
    @5
    f1oeq2
    3syl
    mpbid
    @2
    cB
    @5
    cc0
    cN
    cfzo
    ovex
    f1oen
    @2
    cB
    ensym
    cB
    @2
    hasheni
    4syl
    @0
    @8
    @3
    cN
    wceq
    @9
    cN
    hashfzo0
    syl
    eqtrd
end
