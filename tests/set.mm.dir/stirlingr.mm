include "cn.mm"
include "cv.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "wbr.mm"
include "cli.mm"
include "stirling.mm"
include "wb.mm"
include "wtru.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cr.mm"
include "wf.mm"
include "eqid.mm"
include "wcel.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "nnre.mm"
include "3syl.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "csqrt.mm"
include "ceu.mm"
include "cexp.mm"
include "crp.mm"
include "wceq.mm"
include "2re.mm"
include "a1i.mm"
include "pire.mm"
include "remulcld.mm"
include "cc0.mm"
include "0re.mm"
include "clt.mm"
include "2pos.mm"
include "ltled.mm"
include "cle.mm"
include "pipos.mm"
include "ltleii.mm"
include "mulge0d.mm"
include "nn0ge0d.mm"
include "resqrtcld.mm"
include "ere.mm"
include "wne.mm"
include "epos.mm"
include "gtneii.mm"
include "redivcld.mm"
include "reexpcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "2rp.mm"
include "pirp.mm"
include "rpmulcld.mm"
include "nnrp.mm"
include "rpsqrtcld.mm"
include "epr.mm"
include "rpdivcld.mm"
include "nnz.mm"
include "rpexpcld.mm"
include "eqeltrd.mm"
include "rerpdivcld.mm"
include "fmpti.mm"
include "climreeq.mm"
include "trud.mm"
include "mpbir.mm"

theorem stirlingr
  let cR: class R
  let cS: class S
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x
  assume stirlingr.1: |- S = ( n e. NN0 |-> ( ( sqrt ` ( ( 2 x. _pi ) x. n ) ) x. ( ( n / _e ) ^ n ) ) )
  assume stirlingr.2: |- R = ( ~~>t ` ( topGen ` ran (,) ) )


  assert |- ( n e. NN |-> ( ( ! ` n ) / ( S ` n ) ) ) R 1

  proof
    vn
    cn
    vn
    cv
    #
    cfa
    cfv
    #
    @0
    cS
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    c1
    cR
    wbr
    #
    @4
    c1
    cli
    wbr
    #
    cS
    vn
    stirlingr.1
    stirling
    @5
    @6
    wb
    wtru
    c1
    cR
    @4
    c1
    cn
    stirlingr.2
    nnuz
    wtru
    1zzd
    cn
    cr
    @4
    wf
    wtru
    vn
    cn
    cr
    @3
    @4
    @4
    eqid
    @0
    cn
    wcel
    #
    @1
    @2
    @7
    @0
    cn0
    wcel
    #
    @1
    cn
    wcel
    @1
    cr
    wcel
    @0
    nnnn0
    #
    @0
    faccl
    @1
    nnre
    3syl
    @7
    @2
    c2
    cpi
    cmul
    co
    #
    @0
    cmul
    co
    #
    csqrt
    cfv
    #
    @0
    ceu
    cdiv
    co
    #
    @0
    cexp
    co
    #
    cmul
    co
    #
    crp
    @7
    @8
    @15
    cr
    wcel
    @2
    @15
    wceq
    @9
    @7
    @12
    @14
    @7
    @11
    @7
    @10
    @0
    @7
    c2
    cpi
    c2
    cr
    wcel
    @7
    2re
    a1i
    #
    cpi
    cr
    wcel
    @7
    pire
    a1i
    #
    remulcld
    #
    @0
    nnre
    #
    remulcld
    @7
    @10
    @0
    @18
    @19
    @7
    c2
    cpi
    @16
    @17
    @7
    cc0
    c2
    cc0
    cr
    wcel
    @7
    0re
    a1i
    @16
    cc0
    c2
    clt
    wbr
    @7
    2pos
    a1i
    ltled
    cc0
    cpi
    cle
    wbr
    @7
    cc0
    cpi
    0re
    pire
    pipos
    ltleii
    a1i
    mulge0d
    @7
    @0
    @9
    nn0ge0d
    mulge0d
    resqrtcld
    @7
    @13
    @0
    @7
    @0
    ceu
    @19
    ceu
    cr
    wcel
    @7
    ere
    a1i
    ceu
    cc0
    wne
    @7
    cc0
    ceu
    0re
    epos
    gtneii
    a1i
    redivcld
    @9
    reexpcld
    remulcld
    vn
    cn0
    @15
    cr
    cS
    stirlingr.1
    fvmpt2
    syl2anc
    @7
    @12
    @14
    @7
    @11
    @7
    @10
    @0
    @7
    c2
    cpi
    c2
    crp
    wcel
    @7
    2rp
    a1i
    cpi
    crp
    wcel
    @7
    pirp
    a1i
    rpmulcld
    @0
    nnrp
    #
    rpmulcld
    rpsqrtcld
    @7
    @13
    @0
    @7
    @0
    ceu
    @20
    ceu
    crp
    wcel
    @7
    epr
    a1i
    rpdivcld
    @0
    nnz
    rpexpcld
    rpmulcld
    eqeltrd
    rerpdivcld
    fmpti
    a1i
    climreeq
    trud
    mpbir
end
