include "cfn.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c3.mm"
include "w3a.mm"
include "wceq.mm"
include "c2.mm"
include "w3o.mm"
include "cv.mm"
include "csn.mm"
include "cpr.mm"
include "ctp.mm"
include "wex.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn01to3.mm"
include "syl3an1.mm"
include "wi.mm"
include "wa.mm"
include "hash1snb.mm"
include "biimpa.mm"
include "3mix1.mm"
include "2eximi.mm"
include "19.23bi.mm"
include "eximi.mm"
include "syl.mm"
include "expcom.mm"
include "hash2pr.mm"
include "3mix2.mm"
include "hash3tr.mm"
include "3mix3.mm"
include "3jaoi.mm"
include "com12.mm"
include "3ad2ant1.mm"
include "mpd.mm"

theorem hash1to3
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint V a
  disjoint V b
  disjoint V c
  disjoint a b
  disjoint a c
  disjoint b c
  assert |- ( ( V e. Fin /\ 1 <_ ( # ` V ) /\ ( # ` V ) <_ 3 ) -> E. a E. b E. c ( V = { a } \/ V = { a , b } \/ V = { a , b , c } ) )

  proof
    cV
    cfn
    wcel
    #
    c1
    cV
    chash
    cfv
    #
    cle
    wbr
    #
    @1
    c3
    cle
    wbr
    #
    w3a
    @1
    c1
    wceq
    #
    @1
    c2
    wceq
    #
    @1
    c3
    wceq
    #
    w3o
    #
    cV
    va
    cv
    #
    csn
    wceq
    #
    cV
    @8
    vb
    cv
    #
    cpr
    wceq
    #
    cV
    @8
    @10
    vc
    cv
    ctp
    wceq
    #
    w3o
    #
    vc
    wex
    #
    vb
    wex
    #
    va
    wex
    #
    @0
    @1
    cn0
    wcel
    @2
    @3
    @7
    cV
    hashcl
    @1
    nn01to3
    syl3an1
    @0
    @2
    @7
    @16
    wi
    @3
    @7
    @0
    @16
    @4
    @0
    @16
    wi
    @5
    @6
    @0
    @4
    @16
    @0
    @4
    wa
    @9
    va
    wex
    #
    @16
    @0
    @4
    @17
    cV
    cfn
    va
    hash1snb
    biimpa
    @9
    @15
    va
    @9
    @15
    vc
    @9
    vc
    wex
    @15
    vb
    @9
    @13
    vb
    vc
    @9
    @11
    @12
    3mix1
    2eximi
    19.23bi
    19.23bi
    eximi
    syl
    expcom
    @0
    @5
    @16
    @0
    @5
    wa
    @11
    vb
    wex
    va
    wex
    @16
    cV
    cfn
    va
    vb
    hash2pr
    @11
    @14
    va
    vb
    @11
    @14
    vc
    @11
    @13
    vc
    @11
    @9
    @12
    3mix2
    eximi
    19.23bi
    2eximi
    syl
    expcom
    @0
    @6
    @16
    @0
    @6
    wa
    @12
    vc
    wex
    #
    vb
    wex
    va
    wex
    @16
    cV
    cfn
    va
    vb
    vc
    hash3tr
    @18
    @14
    va
    vb
    @12
    @13
    vc
    @12
    @9
    @11
    3mix3
    eximi
    2eximi
    syl
    expcom
    3jaoi
    com12
    3ad2ant1
    mpd
end
