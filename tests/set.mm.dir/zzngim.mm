include "zring.mm"
include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "cz.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "crg.mm"
include "crh.mm"
include "cc0.mm"
include "cn0.mm"
include "ccrg.mm"
include "0nn0.mm"
include "zncrng.mm"
include "crngring.mm"
include "mp2b.mm"
include "zrhrhm.mm"
include "rhmghm.mm"
include "eqid.mm"
include "cres.mm"
include "czrh.mm"
include "wfo.mm"
include "wfn.mm"
include "wceq.mm"
include "znzrhfo.mm"
include "ax-mp.mm"
include "fofn.mm"
include "fnresdm.mm"
include "reseq1i.mm"
include "eqtr3i.mm"
include "cfzo.mm"
include "cif.mm"
include "iftruei.mm"
include "eqcomi.mm"
include "znf1o.mm"
include "zringbas.mm"
include "isgim.mm"
include "mpbir2an.mm"

theorem zzngim
  let cL: class L
  let cY: class Y
  assume zzngim.y: |- Y = ( Z/nZ ` 0 )
  assume zzngim.2: |- L = ( ZRHom ` Y )


  assert |- L e. ( ZZring GrpIso Y )

  proof
    cL
    zring
    cY
    cgim
    co
    wcel
    cL
    zring
    cY
    cghm
    co
    wcel
    #
    cz
    cY
    cbs
    cfv
    #
    cL
    wf1o
    #
    cY
    crg
    wcel
    #
    cL
    zring
    cY
    crh
    co
    wcel
    @0
    cc0
    cn0
    wcel
    #
    cY
    ccrg
    wcel
    @3
    0nn0
    cc0
    cY
    zzngim.y
    zncrng
    cY
    crngring
    mp2b
    cY
    cL
    zzngim.2
    zrhrhm
    zring
    cY
    cL
    rhmghm
    mp2b
    @4
    @2
    0nn0
    @1
    cL
    cc0
    cz
    cY
    zzngim.y
    @1
    eqid
    #
    cL
    cz
    cres
    #
    cL
    cY
    czrh
    cfv
    #
    cz
    cres
    cz
    @1
    cL
    wfo
    #
    cL
    cz
    wfn
    @6
    cL
    wceq
    @4
    @8
    0nn0
    @1
    cL
    cc0
    cY
    zzngim.y
    @5
    zzngim.2
    znzrhfo
    ax-mp
    cz
    @1
    cL
    fofn
    cz
    cL
    fnresdm
    mp2b
    cL
    @7
    cz
    zzngim.2
    reseq1i
    eqtr3i
    cc0
    cc0
    wceq
    #
    cz
    cc0
    cc0
    cfzo
    co
    #
    cif
    cz
    @9
    cz
    @10
    cc0
    eqid
    iftruei
    eqcomi
    znf1o
    ax-mp
    cz
    @1
    zring
    cY
    cL
    zringbas
    @5
    isgim
    mpbir2an
end
