include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "cpjh.mm"
include "cmv.mm"
include "co.mm"
include "choccli.mm"
include "chincli.mm"
include "pjhclii.mm"
include "pjsubii.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "hvsubvali.mm"
include "c0v.mm"
include "wceq.mm"
include "inss1.mm"
include "pjss2i.mm"
include "ax-mp.mm"
include "wcel.mm"
include "csh.mm"
include "chshii.mm"
include "shococss.mm"
include "inss2.mm"
include "chsscon3i.mm"
include "mpbi.mm"
include "sstri.mm"
include "pjclii.mm"
include "sselii.mm"
include "pjoc2i.mm"
include "oveq2i.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmul0.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "chil.mm"
include "ax-hvaddid.mm"
include "wa.mm"
include "ssel.mm"
include "mpi.mm"
include "shsubcl.mm"
include "mp3an1.mm"
include "sylancr.mm"
include "pjsslem.mm"
include "sylbi.mm"
include "syl5eqelr.mm"
include "jca.mm"
include "elin.mm"
include "hvsubcli.mm"
include "pjchi.mm"
include "bitr3i.mm"
include "sylib.mm"
include "syl5reqr.mm"

theorem pjssmii
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H
  assume pjsslem.1: |- G e. CH


  assert |- ( H C_ G -> ( ( ( projh ` G ) ` A ) -h ( ( projh ` H ) ` A ) ) = ( ( projh ` ( G i^i ( _|_ ` H ) ) ) ` A ) )

  proof
    cH
    cG
    wss
    #
    cA
    cG
    cH
    cort
    cfv
    #
    cin
    #
    cpjh
    cfv
    #
    cfv
    #
    cA
    cG
    cpjh
    cfv
    cfv
    #
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cmv
    co
    #
    @3
    cfv
    #
    @7
    @8
    @5
    @3
    cfv
    #
    @6
    @3
    cfv
    #
    cmv
    co
    #
    @4
    @5
    @6
    @2
    cG
    @1
    pjsslem.1
    cH
    pjidm.1
    choccli
    #
    chincli
    #
    cA
    cG
    pjsslem.1
    pjidm.2
    pjhclii
    #
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    #
    pjsubii
    @11
    @9
    c1
    cneg
    #
    @10
    csm
    co
    #
    cva
    co
    #
    @4
    @9
    @10
    @5
    @2
    @13
    @14
    pjhclii
    @6
    @2
    @13
    @15
    pjhclii
    hvsubvali
    @18
    @4
    c0v
    cva
    co
    #
    @4
    @9
    @4
    @17
    c0v
    cva
    @2
    cG
    wss
    @9
    @4
    wceq
    cG
    @1
    inss1
    cA
    cG
    @2
    @13
    pjidm.2
    pjsslem.1
    pjss2i
    ax-mp
    @17
    @16
    c0v
    csm
    co
    #
    c0v
    @10
    c0v
    @16
    csm
    @6
    @2
    cort
    cfv
    #
    wcel
    @10
    c0v
    wceq
    cH
    @21
    @6
    cH
    @1
    cort
    cfv
    #
    @21
    cH
    csh
    wcel
    cH
    @22
    wss
    cH
    pjidm.1
    chshii
    cH
    shococss
    ax-mp
    @2
    @1
    wss
    @22
    @21
    wss
    cG
    @1
    inss2
    @2
    @1
    @13
    @12
    chsscon3i
    mpbi
    sstri
    cA
    cH
    pjidm.1
    pjidm.2
    pjclii
    #
    sselii
    @6
    @2
    @13
    @15
    pjoc2i
    mpbi
    oveq2i
    @16
    cc
    wcel
    @20
    c0v
    wceq
    neg1cn
    @16
    hvmul0
    ax-mp
    eqtri
    oveq12i
    @4
    chil
    wcel
    @19
    @4
    wceq
    cA
    @2
    @13
    pjidm.2
    pjhclii
    @4
    ax-hvaddid
    ax-mp
    eqtri
    eqtri
    eqtri
    @0
    @7
    cG
    wcel
    #
    @7
    @1
    wcel
    #
    wa
    #
    @8
    @7
    wceq
    #
    @0
    @24
    @25
    @0
    @5
    cG
    wcel
    #
    @6
    cG
    wcel
    #
    @24
    cA
    cG
    pjsslem.1
    pjidm.2
    pjclii
    @0
    @6
    cH
    wcel
    @29
    @23
    cH
    cG
    @6
    ssel
    mpi
    cG
    csh
    wcel
    @28
    @29
    @24
    cG
    pjsslem.1
    chshii
    @5
    @6
    cG
    shsubcl
    mp3an1
    sylancr
    @0
    @7
    cA
    @1
    cpjh
    cfv
    cfv
    #
    cA
    cG
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    cmv
    co
    #
    @1
    cA
    cG
    cH
    pjidm.1
    pjidm.2
    pjsslem.1
    pjsslem
    @0
    @31
    @1
    wss
    #
    @33
    @1
    wcel
    #
    cH
    cG
    pjidm.1
    pjsslem.1
    chsscon3i
    @34
    @30
    @1
    wcel
    #
    @32
    @1
    wcel
    #
    @35
    cA
    @1
    @12
    pjidm.2
    pjclii
    @34
    @32
    @31
    wcel
    @37
    cA
    @31
    cG
    pjsslem.1
    choccli
    pjidm.2
    pjclii
    @31
    @1
    @32
    ssel
    mpi
    @1
    csh
    wcel
    @36
    @37
    @35
    @1
    @12
    chshii
    @30
    @32
    @1
    shsubcl
    mp3an1
    sylancr
    sylbi
    syl5eqelr
    jca
    @26
    @7
    @2
    wcel
    @27
    @7
    cG
    @1
    elin
    @7
    @2
    @13
    @5
    @6
    @14
    @15
    hvsubcli
    pjchi
    bitr3i
    sylib
    syl5reqr
end
