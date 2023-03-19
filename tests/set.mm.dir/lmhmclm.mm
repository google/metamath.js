include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cbs.mm"
include "cress.mm"
include "wceq.mm"
include "csubrg.mm"
include "w3a.mm"
include "cclm.mm"
include "lmhmlmod1.mm"
include "lmhmlmod2.mm"
include "2thd.mm"
include "eqid.mm"
include "lmhmsca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "isclm.mm"
include "3bitr4g.mm"

theorem lmhmclm
  let cS: class S
  let cT: class T
  let cF: class F


  assert |- ( F e. ( S LMHom T ) -> ( S e. CMod <-> T e. CMod ) )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cS
    clmod
    wcel
    #
    cS
    csca
    cfv
    #
    ccnfld
    @2
    cbs
    cfv
    #
    cress
    co
    #
    wceq
    #
    @3
    ccnfld
    csubrg
    cfv
    #
    wcel
    #
    w3a
    cT
    clmod
    wcel
    #
    cT
    csca
    cfv
    #
    ccnfld
    @9
    cbs
    cfv
    #
    cress
    co
    #
    wceq
    #
    @10
    @6
    wcel
    #
    w3a
    cS
    cclm
    wcel
    cT
    cclm
    wcel
    @0
    @1
    @8
    @5
    @12
    @7
    @13
    @0
    @1
    @8
    cS
    cT
    cF
    lmhmlmod1
    cS
    cT
    cF
    lmhmlmod2
    2thd
    @0
    @2
    @9
    @4
    @11
    @0
    @9
    @2
    cS
    cT
    cF
    @2
    @9
    @2
    eqid
    #
    @9
    eqid
    #
    lmhmsca
    eqcomd
    #
    @0
    @3
    @10
    ccnfld
    cress
    @0
    @2
    @9
    cbs
    @16
    fveq2d
    #
    oveq2d
    eqeq12d
    @0
    @3
    @10
    @6
    @17
    eleq1d
    3anbi123d
    @2
    @3
    cS
    @14
    @3
    eqid
    isclm
    @9
    @10
    cT
    @15
    @10
    eqid
    isclm
    3bitr4g
end
